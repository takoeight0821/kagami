{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Griff.Typing (typeCheck, transType, applySubst, readMetaTv, zonkType) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Tuple.Extra (dupe)
import Language.Griff.Extension
import Language.Griff.Grouping
import Language.Griff.RnEnv as R
import Language.Griff.Syntax hiding (Type (..))
import qualified Language.Griff.Syntax as S
import Language.Griff.TcEnv as T
import Language.Griff.Type
import Language.Malgo.Id
import Language.Malgo.Monad
import Language.Malgo.Prelude
import Language.Malgo.Pretty
import Text.Megaparsec.Pos (SourcePos)
import qualified Text.PrettyPrint as P

---------------------------
-- Read and Write MetaTv --
---------------------------

newMetaTv :: (MonadUniq f, MonadIO f) => Kind -> f MetaTv
newMetaTv k = MetaTv <$> getUniq <*> pure k <*> newIORef Nothing

readMetaTv :: MonadIO m => MetaTv -> m (Maybe Type)
readMetaTv (MetaTv _ _ ref) = readIORef ref

writeMetaTv :: MonadIO m => MetaTv -> Type -> m ()
writeMetaTv (MetaTv _ k ref) t
  | k == kind t = writeIORef ref (Just t)
  | otherwise = errorDoc $ "Panic!" <+> "Kind of" <+> pPrint t <+> "is not" <+> pPrint k

-------------
-- Zonking --
-------------

zonkScheme :: MonadIO f => Scheme -> f Scheme
zonkScheme (Forall as t) = Forall as <$> zonkType t

zonkType :: MonadIO f => Type -> f Type
zonkType (TyMeta tv) = do
  mty <- readMetaTv tv
  case mty of
    Just ty -> zonkType ty
    Nothing -> pure $ TyMeta tv
zonkType (TyApp t1 t2) = TyApp <$> zonkType t1 <*> zonkType t2
zonkType (TyArr t1 t2) = TyArr <$> zonkType t1 <*> zonkType t2
zonkType (TyTuple ts) = TyTuple <$> traverse zonkType ts
zonkType (TyLazy t) = TyLazy <$> zonkType t
zonkType t = pure t

--------------------------------
-- Generalize and Instantiate --
--------------------------------

generalize :: (MonadIO m, MonadUniq m) => TcEnv -> Type -> m Scheme
generalize env t = do
  fvs <- toList <$> freeMetaTvs env t
  as <- traverse (\(tv, nameChar) -> newId (kind tv) $ T.singleton nameChar) (zip fvs ['a' ..])
  zipWithM_ writeMetaTv fvs (map TyVar as)
  Forall as <$> zonkType t

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

instantiate :: (MonadUniq m, MonadIO m) => Scheme -> m Type
instantiate (Forall as t) = do
  vs <- traverse (\a -> TyMeta <$> newMetaTv (kind a)) as
  applySubst (Map.fromList $ zip as vs) <$> zonkType t

applySubst :: Map TyVar Type -> Type -> Type
applySubst subst (TyVar v) = fromMaybe (TyVar v) $ Map.lookup v subst
applySubst subst (TyApp t1 t2) = TyApp (applySubst subst t1) (applySubst subst t2)
applySubst subst (TyArr t1 t2) = TyArr (applySubst subst t1) (applySubst subst t2)
applySubst subst (TyTuple ts) = TyTuple $ map (applySubst subst) ts
applySubst subst (TyLazy t) = TyLazy $ applySubst subst t
applySubst _ t = t

-----------------
-- Unification --
-----------------

unify :: (HasCallStack, MonadIO m) => SourcePos -> Type -> Type -> m ()
unify pos t1 t2 = do
  t1' <- zonkType t1
  t2' <- zonkType t2
  (t1', t2') & \case
    (TyMeta tv1, TyMeta tv2) | tv1 == tv2 -> pure ()
    (TyMeta tv, t) -> unifyMeta pos tv t
    (t, TyMeta tv) -> unifyMeta pos tv t
    (TyApp t11 t12, TyApp t21 t22) -> do
      unify pos t11 t21
      unify pos t12 t22
    (TyArr t11 t12, TyArr t21 t22) -> do
      unify pos t11 t21
      unify pos t12 t22
    (TyTuple ts1, TyTuple ts2) -> zipWithM_ (unify pos) ts1 ts2
    (TyLazy t1, TyLazy t2) -> unify pos t1 t2
    (t1, t2)
      | t1 == t2 -> pure ()
      | otherwise -> errorOn pos $ "Type mismatch:" <+> P.vcat [pPrint t1, pPrint t2]

unifyMeta :: (HasCallStack, MonadIO m) => SourcePos -> MetaTv -> Type -> m ()
unifyMeta pos tv t2
  | kind tv /= kind t2 = errorOn pos $ "Kind mismatch:" <+> P.vcat [P.quotes $ pPrint tv, pPrint t2]
  | otherwise = do
    mt1 <- readMetaTv tv
    case mt1 of
      Just t1 -> unify pos t1 t2
      Nothing -> do
        if tv `elem` metaTvs t2
          then errorOn pos $ "Occurs check" <+> P.quotes (pPrint tv) <+> "for" <+> pPrint t2
          else writeMetaTv tv t2

typeCheck :: (MonadUniq m, MonadIO m, MonadFail m) => RnEnv -> [Decl (Griff 'Rename)] -> m (BindGroup (Griff 'TypeCheck), TcEnv)
typeCheck rnEnv ds = do
  tcEnv <- genTcEnv rnEnv
  runReaderT (tcDecls ds) tcEnv

tcDecls :: (MonadUniq m, MonadReader TcEnv m, MonadIO m, MonadFail m) => [Decl (Griff 'Rename)] -> m (BindGroup (Griff 'TypeCheck), TcEnv)
tcDecls ds = do
  let bindGroup = makeBindGroup ds
  (env, dataDefs') <- tcDataDefs (bindGroup ^. dataDefs)

  local (env <>) $ do
    (env, forigns') <- tcForigns (bindGroup ^. forigns)

    local (env <>) $ do
      (env, scSigs') <- tcScSigs (bindGroup ^. scSigs)

      local (env <>) $ do
        env <- mconcat <$> traverse prepareTcScDefs (bindGroup ^. scDefs)
        local (over T.varEnv (env <>)) $ do
          (env, scDefs') <- tcScDefGroup (bindGroup ^. scDefs)
          local (env <>) $ do
            env <-
              ask >>= T.varEnv (traverse zonkScheme)
                >>= T.typeEnv (traverse zonkType)
                >>= T.tyConEnv (traverse $ rtraverse $ traverse $ rtraverse zonkType)
            pure
              ( BindGroup
                  { _dataDefs = dataDefs',
                    _infixs = [],
                    _forigns = forigns',
                    _scSigs = scSigs',
                    _scDefs = scDefs'
                  },
                env
              )

lookupType :: (MonadReader TcEnv m) => SourcePos -> RnTId -> m Type
lookupType pos name = do
  mtype <- Map.lookup name <$> view T.typeEnv
  case mtype of
    Nothing -> errorOn pos $ "Not in scope:" <+> P.quotes (pPrint name)
    Just typ -> pure typ

lookupVar :: (MonadReader TcEnv m) => SourcePos -> RnId -> m Scheme
lookupVar pos name = do
  mscheme <- Map.lookup name <$> view T.varEnv
  case mscheme of
    Nothing -> errorOn pos $ "Not in scope:" <+> P.quotes (pPrint name)
    Just scheme -> pure scheme

tcDataDefs :: (MonadReader TcEnv m, MonadIO m, MonadUniq m, MonadFail m) => [DataDef (Griff 'Rename)] -> m (TcEnv, [DataDef (Griff 'TypeCheck)])
tcDataDefs ds = do
  dataEnv <- foldMapA ?? ds $ \(_, name, params, _) -> do
    con <- newId (kindof params) (name ^. idName)
    pure $ Map.singleton name (TyCon con)
  (conEnvs, ds') <- local (over T.typeEnv (dataEnv <>)) $
    mapAndUnzipM ?? ds $ \(pos, name, params, cons) -> do
      (dataTypes, cons') <- mapAndUnzipM ?? cons $ \(con, args) -> do
        paramsEnv <- foldMapA (\p -> Map.singleton p . TyMeta <$> newMetaTv Star) params
        local (over T.typeEnv (paramsEnv <>)) $ do
          (dataType, conType) <- buildType pos name params args
          pure (dataType, (con, conType))
      traverse_ (unify pos (head dataTypes)) (tail dataTypes)
      Just (TyCon dataName) <- Map.lookup name <$> view T.typeEnv
      fvs <- Set.toList . mconcat <$> traverse (freeMetaTvs mempty <=< zonkType . view _2) cons'
      as <- traverse (\(tv, nameChar) -> newId (kind tv) $ T.singleton nameChar) $ zip fvs ['a' ..]
      zipWithM_ writeMetaTv fvs (map TyVar as)
      pure
        ( mempty & T.varEnv .~ foldMap (\(con, conType) -> Map.singleton con (Forall as conType)) cons'
            & T.tyConEnv .~ Map.singleton dataName (as, cons'),
          (pos, name, params, map (second (map tcType)) cons)
        )
  pure (mconcat conEnvs & T.typeEnv .~ dataEnv, ds')
  where
    kindof [] = Star
    kindof (_ : xs) = KArr Star (kindof xs)
    buildType pos name params [] = do
      name' <- lookupType pos name
      params' <- traverse (lookupType pos) params
      pure $ dupe $ foldr (flip TyApp) name' params'
    buildType pos name params (arg : args) = do
      arg' <- transType $ tcType arg
      (dataType, ret) <- buildType pos name params args
      pure (dataType, TyArr arg' ret)

tcForigns :: (MonadUniq m, MonadIO m, MonadReader TcEnv m) => [Forign (Griff 'Rename)] -> m (TcEnv, [Forign (Griff 'TypeCheck)])
tcForigns ds = fmap (first mconcat) $
  mapAndUnzipM ?? ds $ \(pos, name, ty) -> do
    let tyVars = Set.toList $ getTyVars ty
    tyVars' <- traverse (const $ TyMeta <$> newMetaTv Star) tyVars
    local (over T.typeEnv (Map.fromList (zip tyVars tyVars') <>)) $ do
      scheme@(Forall _ ty') <- generalize mempty =<< transType (tcType ty)
      pure
        ( mempty & T.varEnv .~ Map.fromList [(name, scheme)],
          (WithType pos ty', name, tcType ty)
        )

tcScSigs :: (MonadUniq m, MonadIO m, MonadReader TcEnv m) => [ScSig (Griff 'Rename)] -> m (TcEnv, [ScSig (Griff 'TypeCheck)])
tcScSigs ds = fmap (first mconcat) $
  mapAndUnzipM ?? ds $ \(pos, name, ty) -> do
    let tyVars = Set.toList $ getTyVars ty
    tyVars' <- traverse (const $ TyMeta <$> newMetaTv Star) tyVars
    local (over T.typeEnv (Map.fromList (zip tyVars tyVars') <>)) $ do
      scheme <- generalize mempty =<< transType (tcType ty)
      pure
        ( mempty & T.varEnv .~ Map.singleton name scheme,
          (pos, name, tcType ty)
        )

prepareTcScDefs :: (Foldable f, MonadReader TcEnv m, MonadUniq m, MonadIO m) => f (ScDef (Griff 'Rename)) -> m (Map (Id ()) Scheme)
prepareTcScDefs ds = foldMapA ?? ds $ \(_, name, _, _) -> do
  mscheme <- Map.lookup name <$> view T.varEnv
  case mscheme of
    Nothing -> Map.singleton name . Forall [] . TyMeta <$> newMetaTv Star
    Just _ -> pure mempty

tcScDefGroup :: (MonadReader TcEnv f, MonadUniq f, MonadIO f) => [[ScDef (Griff 'Rename)]] -> f (TcEnv, [[ScDef (Griff 'TypeCheck)]])
tcScDefGroup [] = pure (mempty, [])
tcScDefGroup (ds : dss) = do
  (env, ds') <- tcScDefs ds
  local (env <>) $ do
    (env, dss') <- tcScDefGroup dss
    pure (env <> env, ds' : dss')

tcScDefs :: (MonadReader TcEnv m, MonadUniq m, MonadIO m) => [ScDef (Griff 'Rename)] -> m (TcEnv, [ScDef (Griff 'TypeCheck)])
tcScDefs ds = do
  (nts, defs) <- mapAndUnzipM ?? ds $ \(pos, name, params, expr) -> do
    paramTypes <- traverse (const $ TyMeta <$> newMetaTv Star) params
    local (over T.varEnv (Map.fromList (zip params (map (Forall []) paramTypes)) <>)) $ do
      expr' <- tcExpr expr
      ty <- instantiate =<< lookupVar pos name
      unify pos ty (foldr TyArr (view typeOf expr') paramTypes)
      pure ((name, ty), (WithType pos ty, name, params, expr'))
  fvs <- Set.toList . mconcat <$> traverse (freeMetaTvs mempty <=< zonkType . view _2) nts
  as <- traverse (\(tv, nameChar) -> newId (kind tv) $ T.singleton nameChar) $ zip fvs ['a' ..]
  zipWithM_ writeMetaTv fvs (map TyVar as)
  nts' <- traverse (rtraverse (fmap (Forall as) . zonkType)) nts
  pure
    ( mempty & T.varEnv .~ Map.fromList nts',
      defs
    )

-- coercion
tcType :: S.Type (Griff 'Rename) -> S.Type (Griff 'TypeCheck)
tcType (S.TyApp pos t ts) = S.TyApp pos (tcType t) (map tcType ts)
tcType (S.TyVar pos v) = S.TyVar pos v
tcType (S.TyCon pos c) = S.TyCon pos c
tcType (S.TyArr pos t1 t2) = S.TyArr pos (tcType t1) (tcType t2)
tcType (S.TyTuple pos ts) = S.TyTuple pos $ map tcType ts
tcType (S.TyLazy pos t) = S.TyLazy pos $ tcType t

transType :: (Applicative f, MonadReader TcEnv f) => S.Type (Griff 'TypeCheck) -> f Type
transType (S.TyApp _ t ts) = foldr (flip TyApp) <$> transType t <*> traverse transType ts
transType (S.TyVar pos v) = lookupType pos v
transType (S.TyCon pos c) = lookupType pos c
transType (S.TyArr _ t1 t2) = TyArr <$> transType t1 <*> transType t2
transType (S.TyTuple _ ts) = TyTuple <$> traverse transType ts
transType (S.TyLazy _ t) = TyLazy <$> transType t

tcExpr :: (MonadReader TcEnv m, MonadUniq m, MonadIO m) => Exp (Griff 'Rename) -> m (Exp (Griff 'TypeCheck))
tcExpr (Var pos v) = do
  scheme <- lookupVar pos v
  v' <- instantiate scheme
  pure $ Var (WithType pos $ view typeOf v') v
tcExpr (Con pos c) = do
  c' <- instantiate =<< lookupVar pos c
  pure $ Con (WithType pos $ view typeOf c') c
tcExpr (Unboxed pos u) =
  pure $ Unboxed (WithType pos $ view typeOf u) u
tcExpr (Apply pos f x) = do
  f' <- tcExpr f
  x' <- tcExpr x
  retType <- TyMeta <$> newMetaTv Star
  unify pos (view typeOf f') (TyArr (view typeOf x') retType)
  pure $ Apply (WithType pos retType) f' x'
tcExpr (OpApp x@(pos, _) op e1 e2) = do
  e1' <- tcExpr e1
  e2' <- tcExpr e2
  opType <- instantiate =<< lookupVar pos op
  retType <- TyMeta <$> newMetaTv Star
  unify pos opType (TyArr (view typeOf e1') $ TyArr (view typeOf e2') retType)
  pure $ OpApp (WithType x retType) op e1' e2'
tcExpr (Fn pos (Clause x [] e : _)) = do
  e' <- tcExpr e
  pure $ Fn (WithType pos (TyLazy $ e' ^. typeOf)) (Clause (WithType x (TyLazy $ e' ^. typeOf)) [] e' : [])
tcExpr (Fn pos cs) = do
  -- TODO: lazy valueを正しく型付けする
  cs' <- traverse tcClause cs
  case cs' of
    (c' : cs') -> do
      traverse_ (unify pos (view typeOf c') . view typeOf) cs'
      pure $ Fn (WithType pos (view typeOf c')) (c' : cs')
    _ -> bug Unreachable
tcExpr (Tuple pos es) = do
  es' <- traverse tcExpr es
  pure $ Tuple (WithType pos (TyTuple (map (view typeOf) es'))) es'
tcExpr (Force pos e) = do
  e' <- tcExpr e
  ty <- TyMeta <$> newMetaTv Star
  unify pos (TyLazy ty) (view typeOf e')
  pure $ Force (WithType pos ty) e'

tcClause :: (MonadReader TcEnv m, MonadIO m, MonadUniq m) => Clause (Griff 'Rename) -> m (Clause (Griff 'TypeCheck))
tcClause (Clause pos patterns expr) = do
  (env, patterns') <- tcPatterns patterns
  local (env <>) $ do
    expr' <- tcExpr expr
    let ty = foldr (TyArr . view typeOf) (view typeOf expr') patterns'
    pure $ Clause (WithType pos ty) patterns' expr'

tcPatterns :: (MonadUniq m, MonadIO m, MonadReader TcEnv m) => [Pat (Griff 'Rename)] -> m (TcEnv, [Pat (Griff 'TypeCheck)])
tcPatterns ps = fmap (first mconcat) $
  mapAndUnzipM ?? ps $ \case
    VarP x v -> do
      vscheme@(Forall _ ty) <- Forall [] . TyMeta <$> newMetaTv Star
      pure
        ( mempty & T.varEnv .~ Map.singleton v vscheme,
          VarP (WithType x ty) v
        )
    ConP pos con pats -> do
      (env, pats') <- tcPatterns pats
      local (env <>) $ do
        conType <- instantiate =<< lookupVar pos con
        ty <- TyMeta <$> newMetaTv Star
        unify pos conType (foldr (TyArr . view typeOf) ty pats')
        pure (env, ConP (WithType pos ty) con pats')
    UnboxedP pos unboxed -> do
      pure (mempty, UnboxedP (WithType pos (view typeOf unboxed)) unboxed)