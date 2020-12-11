{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Griff.TypeCheck (typeCheck, applySubst) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Koriel.Id
import Koriel.MonadUniq
import Koriel.Pretty
import Language.Griff.Interface
import Language.Griff.Prelude
import Language.Griff.Rename.RnEnv (RnEnv)
import Language.Griff.Syntax hiding (Type (..))
import qualified Language.Griff.Syntax as S
import Language.Griff.Syntax.Extension
import Language.Griff.Syntax.Grouping
import Language.Griff.Type
import Language.Griff.TypeCheck.Constraint
import Language.Griff.TypeCheck.TcEnv
import qualified Language.Griff.TypeCheck.TcEnv as T
import Text.Megaparsec (SourcePos)

-- Entry point
typeCheck :: (MonadUniq m, MonadIO m, MonadGriff m) => RnEnv -> [Decl (Griff 'Rename)] -> m (TcEnv, BindGroup (Griff 'TypeCheck))
typeCheck rnEnv ds = do
  tcEnv <- genTcEnv rnEnv
  runReaderT (tcBindGroup $ makeBindGroup ds) tcEnv

tcBindGroup :: (MonadUniq m, MonadReader TcEnv m, MonadIO m, MonadGriff m) => BindGroup (Griff 'Rename) -> m (TcEnv, BindGroup (Griff 'TypeCheck))
tcBindGroup bindGroup = do
  (imports', updater) <- tcImports $ bindGroup ^. imports
  local updater do
    (dataDefs', updater) <- tcDataDefs $ bindGroup ^. dataDefs
    local updater do
      (foreigns', env) <- tcForeigns $ bindGroup ^. foreigns
      local (env <>) do
        (scSigs', env) <- tcScSigs $ bindGroup ^. scSigs
        local (env <>) do
          env <- foldMapA prepareTcScDefs $ bindGroup ^. scDefs
          local (over T.varEnv (env <>)) do
            (scDefs', env) <- tcScDefGroup $ bindGroup ^. scDefs
            local (env <>) do
              env <-
                ask >>= traverseOf (T.varEnv . traversed) zonkScheme
                  >>= traverseOf (T.typeEnv . traversed . overTypeDef) zonkType
              foreigns'' <- traverseOf (traversed . _1) (overType zonkType) foreigns'
              scDefs'' <-
                traverseOf (traversed . traversed . _1) (overType zonkType)
                  =<< traverseOf (traversed . traversed . _4) (overType zonkType) scDefs'
              pure
                ( env,
                  BindGroup
                    { _dataDefs = dataDefs',
                      _infixs = [],
                      _foreigns = foreigns'',
                      _scSigs = scSigs',
                      _scDefs = scDefs'',
                      _imports = imports'
                    }
                )

tcImports :: (MonadGriff f, MonadIO f) => [Import (Griff 'Rename)] -> f ([Import (Griff 'TypeCheck)], TcEnv -> TcEnv)
tcImports ds = second (appEndo . mconcat) <$> mapAndUnzipM tcImport ds
  where
    tcImport (pos, modName) = do
      interface <- loadInterface modName
      pure ((pos, modName), Endo $ (varEnv <>~ interface ^. signatureMap) . (typeEnv <>~ interface ^. typeDefMap))

tcDataDefs ::
  (MonadReader TcEnv m, MonadIO m, MonadUniq m, MonadGriff m) =>
  [DataDef (Griff 'Rename)] ->
  m ([DataDef (Griff 'TypeCheck)], TcEnv -> TcEnv)
tcDataDefs ds = do
  -- 相互再帰的な型定義がありうるため、型コンストラクタに対応するTyConを生成する
  dataEnv <- foldMapA ?? ds $ \(_, name, params, _) -> Map.singleton name . simpleTypeDef . TyCon <$> newId (name ^. idName) (kindof params)
  local (over T.typeEnv (dataEnv <>)) do
    (ds', conEnvs) <- mapAndUnzipM ?? ds $ \(pos, name, params, cons) -> do
      paramsEnv <- foldMapA ?? params $ \p -> Map.singleton p . simpleTypeDef . TyMeta <$> newMetaTv Star ""
      local (over T.typeEnv (paramsEnv <>)) do
        cons' <- traverseOf (traversed . _2) ?? cons $ \args -> do
          -- 値コンストラクタの型を構築
          name' <- lookupType pos name
          params' <- traverse (lookupType pos) params
          args' <- traverse transType args
          pure $ foldr TyArr (foldr (flip TyApp) name' params') args'
        (as, cons'') <- generalizeMutRecs mempty cons'
        pure
          ( (pos, name, params, map (second (map tcType)) cons),
            Endo $
              (T.varEnv <>~ Map.fromList cons'')
                . (T.typeEnv . at name . _Just . qualVars .~ as)
                . (T.typeEnv . at name . _Just . union .~ cons')
          )
    pure (ds', appEndo (mconcat conEnvs) . (T.typeEnv <>~ dataEnv))
  where
    kindof [] = Star
    kindof (_ : xs) = KArr Star (kindof xs)

tcForeigns ::
  (MonadUniq m, MonadIO m, MonadReader TcEnv m, MonadGriff m) =>
  [Foreign (Griff 'Rename)] ->
  m ([Foreign (Griff 'TypeCheck)], TcEnv)
tcForeigns ds = fmap (second mconcat) $
  mapAndUnzipM ?? ds $ \(pos, name, ty) -> do
    tyVars <- traverse (\tyVar -> (tyVar,) . simpleTypeDef . TyMeta <$> newMetaTv Star (show $ pPrint tyVar)) $ Set.toList $ getTyVars ty
    local (over T.typeEnv (Map.fromList tyVars <>)) do
      scheme@(Forall _ ty') <- generalize mempty =<< transType ty
      pure ((WithType pos ty', name, tcType ty), mempty & T.varEnv .~ Map.fromList [(name, scheme)])

tcScSigs ::
  (MonadUniq m, MonadIO m, MonadReader TcEnv m, MonadGriff m) =>
  [ScSig (Griff 'Rename)] ->
  m ([ScSig (Griff 'TypeCheck)], TcEnv)
tcScSigs ds = fmap (second mconcat) $
  mapAndUnzipM ?? ds $ \(pos, name, ty) -> do
    tyVars <- traverse (\tyVar -> (tyVar,) . simpleTypeDef . TyMeta <$> newMetaTv Star (show $ pPrint tyVar)) $ Set.toList $ getTyVars ty
    local (over T.typeEnv (Map.fromList tyVars <>)) do
      scheme <- generalize mempty =<< transType ty
      pure ((pos, name, tcType ty), mempty & T.varEnv .~ Map.singleton name scheme)

-- ScSigによる型注釈がないScDefの暫定的な型を生成する
prepareTcScDefs ::
  (MonadReader TcEnv m, MonadUniq m, MonadIO m) =>
  [ScDef (Griff 'Rename)] ->
  m (Map RnId Scheme)
prepareTcScDefs ds = foldMapA ?? ds $ \(_, name, _, _) -> do
  mscheme <- view $ T.varEnv . at name
  case mscheme of
    Nothing -> Map.singleton name . Forall [] . TyMeta <$> newMetaTv Star ""
    Just _ -> pure mempty

tcScDefGroup ::
  (MonadReader TcEnv f, MonadUniq f, MonadIO f, MonadGriff f) =>
  [[ScDef (Griff 'Rename)]] ->
  f ([[ScDef (Griff 'TypeCheck)]], TcEnv)
tcScDefGroup [] = pure ([], mempty)
tcScDefGroup (ds : dss) = do
  (ds', env) <- tcScDefs ds
  local (env <>) do
    (dss', env') <- tcScDefGroup dss
    pure (ds' : dss', env <> env')

tcScDefs ::
  (MonadReader TcEnv m, MonadUniq m, MonadIO m, MonadGriff m) =>
  [ScDef (Griff 'Rename)] ->
  m ([ScDef (Griff 'TypeCheck)], TcEnv)
tcScDefs ds = do
  (ds', nts) <- mapAndUnzipM ?? ds $ \(pos, name, params, expr) -> do
    paramTypes <- traverse (const $ TyMeta <$> newMetaTv Star "") params
    local (over T.varEnv (Map.fromList (zip params (map (Forall []) paramTypes)) <>)) do
      (expr', wanted) <- runWriterT (tcExpr expr)
      ty <- instantiate True =<< lookupVar pos name
      solve $ eqCons pos ty (foldr TyArr (expr' ^. toType) paramTypes) : wanted
      pure ((WithType pos ty, name, params, expr'), (name, ty))
  (_, nts') <- generalizeMutRecs mempty nts
  pure (ds', mempty & T.varEnv .~ Map.fromList nts')

tcExpr ::
  (MonadReader TcEnv m, MonadUniq m, MonadIO m, MonadGriff m) =>
  Exp (Griff 'Rename) ->
  WriterT [WithPos] m (Exp (Griff 'TypeCheck))
tcExpr (Var pos v) = do
  vType <- instantiate False =<< lookupVar pos v
  pure $ Var (WithType pos vType) v
tcExpr (Con pos c) = do
  cType <- instantiate False =<< lookupVar pos c
  pure $ Con (WithType pos cType) c
tcExpr (Unboxed pos u) = pure $ Unboxed (WithType pos $ u ^. toType) u
tcExpr (Apply pos f x) = do
  f' <- tcExpr f
  x' <- tcExpr x
  retType <- TyMeta <$> newMetaTv Star ""
  tell [eqCons pos (f' ^. toType) (TyArr (x' ^. toType) retType)]
  pure $ Apply (WithType pos retType) f' x'
tcExpr (OpApp x@(pos, _) op e1 e2) = do
  e1' <- tcExpr e1
  e2' <- tcExpr e2
  opType <- instantiate False =<< lookupVar pos op
  retType <- TyMeta <$> newMetaTv Star ""
  tell [eqCons pos opType (TyArr (e1' ^. toType) $ TyArr (e2' ^. toType) retType)]
  pure $ OpApp (WithType x retType) op e1' e2'
tcExpr (Fn pos (Clause x [] ss : _)) = do
  ss' <- tcStmts ss
  pure $
    Fn
      (WithType pos (TyLazy $ last ss' ^. toType))
      [Clause (WithType x (TyLazy $ last ss' ^. toType)) [] ss']
tcExpr (Fn pos cs) = do
  cs' <- traverse tcClause cs
  case cs' of
    (c' : cs') -> do
      tell $ map (eqCons pos (c' ^. toType) . view toType) cs'
      pure $ Fn (WithType pos (c' ^. toType)) (c' : cs')
    _ -> bug Unreachable
tcExpr (Tuple pos es) = do
  es' <- traverse tcExpr es
  pure $ Tuple (WithType pos (TyTuple (map (view toType) es'))) es'
tcExpr (Force pos e) = do
  e' <- tcExpr e
  ty <- TyMeta <$> newMetaTv Star ""
  tell [eqCons pos (TyLazy ty) (e' ^. toType)]
  pure $ Force (WithType pos ty) e'

tcClause :: (MonadReader TcEnv m, MonadIO m, MonadUniq m, MonadGriff m) => Clause (Griff 'Rename) -> WriterT [WithPos] m (Clause (Griff 'TypeCheck))
tcClause (Clause pos pats ss) = do
  (pats', env) <- tcPatterns pats
  local (env <>) do
    ss' <- tcStmts ss
    pure $ Clause (WithType pos (foldr (TyArr . view toType) (last ss' ^. toType) pats')) pats' ss'

tcStmts :: (MonadReader TcEnv m, MonadIO m, MonadUniq m, MonadGriff m) => [Stmt (Griff 'Rename)] -> WriterT [WithPos] m [Stmt (Griff 'TypeCheck)]
tcStmts [] = pure []
tcStmts (NoBind pos e : ss) = do
  e' <- tcExpr e
  ss' <- tcStmts ss
  pure $ NoBind pos e' : ss'
tcStmts (Let pos v e : ss) = do
  env <- ask
  (e', wanted) <- listen $ tcExpr e
  solve wanted
  -- FIXME: value restriction
  vScheme <- generalize env (e' ^. toType)
  local (over T.varEnv $ Map.insert v vScheme) do
    ss' <- tcStmts ss
    pure $ Let pos v e' : ss'

tcPatterns :: (MonadReader TcEnv m, MonadIO m, MonadUniq m, MonadGriff m) => [Pat (Griff 'Rename)] -> WriterT [WithPos] m ([Pat (Griff 'TypeCheck)], TcEnv)
tcPatterns [] = pure ([], mempty)
tcPatterns (VarP x v : ps) = do
  vscheme@(Forall _ ty) <- Forall [] . TyMeta <$> newMetaTv Star ""
  (ps', env) <- tcPatterns ps
  pure (VarP (WithType x ty) v : ps', env & T.varEnv %~ Map.insert v vscheme)
tcPatterns (ConP pos con pats : ps) = do
  conType <- instantiate False =<< lookupVar pos con
  let (conParams, _) = splitTyArr conType
  -- コンストラクタの型に基づくASTの組み換え
  -- 足りない分を後続のパターン列から補充
  let (morePats, restPs) = splitAt (length conParams - length pats) ps
  -- 足りない分（morePats）を補充した残り（restPs）が空でなければ、
  -- 2引数以上の関数での文法エラー
  if not (null morePats) && not (null restPs)
    then errorOn pos "Invalid Pattern: You may need to put parentheses"
    else pure ()
  (pats', env) <- tcPatterns (pats <> morePats)
  local (env <>) $ do
    ty <- TyMeta <$> newMetaTv Star ""
    tell [eqCons pos conType (foldr (TyArr . view toType) ty pats')]
    (ps', env') <- tcPatterns restPs
    pure (ConP (WithType pos ty) con pats' : ps', env' <> env)
tcPatterns (TupleP pos pats : ps) = do
  (pats', env) <- tcPatterns pats
  local (env <>) do
    (ps', env') <- tcPatterns ps
    pure (TupleP (WithType pos (TyTuple $ map (view toType) pats')) pats' : ps', env <> env')
tcPatterns (UnboxedP pos unboxed : cs) = do
  (ps, env') <- tcPatterns cs
  pure (UnboxedP (WithType pos (unboxed ^. toType)) unboxed : ps, env')

-----------------------------------
-- Translate Type representation --
-----------------------------------

transType :: (MonadReader TcEnv m, MonadIO m, MonadGriff m) => S.Type (Griff 'Rename) -> m Type
transType (S.TyApp _ t ts) = foldr (flip TyApp) <$> transType t <*> traverse transType ts
transType (S.TyVar pos v) = lookupType pos v
transType (S.TyCon pos c) = lookupType pos c
transType (S.TyArr _ t1 t2) = TyArr <$> transType t1 <*> transType t2
transType (S.TyTuple _ ts) = TyTuple <$> traverse transType ts
transType (S.TyLazy _ t) = TyLazy <$> transType t

tcType :: S.Type (Griff 'Rename) -> S.Type (Griff 'TypeCheck)
tcType (S.TyApp pos t ts) = S.TyApp pos (tcType t) (map tcType ts)
tcType (S.TyVar pos v) = S.TyVar pos v
tcType (S.TyCon pos c) = S.TyCon pos c
tcType (S.TyArr pos t1 t2) = S.TyArr pos (tcType t1) (tcType t2)
tcType (S.TyTuple pos ts) = S.TyTuple pos $ map tcType ts
tcType (S.TyLazy pos t) = S.TyLazy pos $ tcType t

-------------------------------
-- Lookup the value of TcEnv --
-------------------------------

lookupType :: (HasCallStack, MonadReader TcEnv m, MonadGriff m, MonadIO m) => SourcePos -> RnTId -> m Type
lookupType pos name = do
  mtype <- preview $ T.typeEnv . at name . _Just . constructor
  case mtype of
    Nothing -> errorOn pos $ "Not in scope:" <+> quotes (pPrint name)
    Just typ -> pure typ

lookupVar :: (HasCallStack, MonadReader TcEnv m, MonadGriff m, MonadIO m) => SourcePos -> RnId -> m Scheme
lookupVar pos name = do
  mscheme <- view $ T.varEnv . at name
  case mscheme of
    Nothing -> errorOn pos $ "Not in scope:" <+> quotes (pPrint name)
    Just scheme -> pure scheme

--------------------------------
-- Generalize and Instantiate --
--------------------------------

-- 型内の自由変数を取り出し、抽象化する
generalize :: (MonadIO m, MonadUniq m) => TcEnv -> Type -> m Scheme
generalize env t = do
  fvs <- toList <$> freeMetaTvs env t
  as <- traverse (\(tv, nameChar) -> newId [nameChar] (kind tv)) (zip fvs ['a' ..])
  zipWithM_ writeMetaTv fvs (map TyVar as)
  Forall as <$> zonkType t

generalizeMutRecs :: (MonadIO m, MonadUniq m) => TcEnv -> [(TcId, Type)] -> m ([Id Kind], [(TcId, Scheme)])
generalizeMutRecs env nts = do
  fvs <- toList . mconcat <$> traverse (freeMetaTvs env <=< zonkType . view _2) nts
  as <- traverse (\(tv, nameChar) -> newId [nameChar] (kind tv)) (zip fvs ['a' ..])
  zipWithM_ writeMetaTv fvs (map TyVar as)
  (as,) <$> traverseOf (traversed . _2) (fmap (Forall as) . zonkType) nts

freeMetaTvs :: MonadIO m => TcEnv -> Type -> m (Set MetaTv)
freeMetaTvs env t = do
  env' <- traverse zonkScheme (view T.varEnv env)
  t' <- zonkType t
  pure $ metaTvs t' Set.\\ foldMap metaTvsScheme env'

metaTvs :: Type -> Set MetaTv
metaTvs (TyApp t1 t2) = metaTvs t1 <> metaTvs t2
metaTvs (TyArr t1 t2) = metaTvs t1 <> metaTvs t2
metaTvs (TyTuple ts) = mconcat $ map metaTvs ts
metaTvs (TyLazy t) = metaTvs t
metaTvs (TyMeta tv) = Set.singleton tv
metaTvs _ = mempty

metaTvsScheme :: Scheme -> Set MetaTv
metaTvsScheme (Forall _ t) = metaTvs t

-- 型を具体化する
instantiate :: (MonadUniq m, MonadIO m) => Bool -> Scheme -> m Type
instantiate isRigit (Forall as t) = do
  vs <- traverse (\a -> TyMeta <$> newMetaTv (kind a) (if isRigit then show $ pPrint a else "")) as
  applySubst (Map.fromList $ zip as vs) <$> zonkType t

applySubst :: Map TyVar Type -> Type -> Type
applySubst subst (TyVar v) = fromMaybe (TyVar v) $ Map.lookup v subst
applySubst subst (TyApp t1 t2) = TyApp (applySubst subst t1) (applySubst subst t2)
applySubst subst (TyArr t1 t2) = TyArr (applySubst subst t1) (applySubst subst t2)
applySubst subst (TyTuple ts) = TyTuple $ map (applySubst subst) ts
applySubst subst (TyLazy t) = TyLazy $ applySubst subst t
applySubst _ t = t