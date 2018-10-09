{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeFamilies     #-}
module Language.Malgo.FrontEnd.TypeCheck (typeCheck, unify, expand, subst, (=:=), generalize, instantiate) where

import           Data.List                      (nub)
import qualified Data.Map                       as Map
import           Language.Malgo.FrontEnd.Loc
import qualified Language.Malgo.FrontEnd.Rename as Rename
import           Language.Malgo.Id
import           Language.Malgo.IR.AST
import           Language.Malgo.Monad
import           Language.Malgo.Type
import           Universum                      hiding (Type)

-- Types

data TymapEntry = Type (Type Id)
                | TyCon (TyCon Id)

data TyEnv = TyEnv { _varmap   :: Map Id (Type Id)
                   , _tymap    :: Map Id TymapEntry
                   , _labelmap :: Map Text (Type Id, Type Id)
                   }

initTyEnv :: Rename.RnEnv -> TyEnv
initTyEnv rnEnv =
  TyEnv
  mempty
  (Map.fromList [ (typeLookup "->", TyCon ArrowC)
                , (typeLookup "Int", TyCon (IntC 64))
                , (typeLookup "Float", TyCon Float32C)
                , (typeLookup "Char", TyCon (IntC 8))]) mempty
  where typeLookup key =
          case Map.lookup key (Rename._tymap rnEnv) of
            Just i  -> i
            Nothing -> error "unreachable(initTyEnv)"

data TcError = UnifyError (Type Id) (Type Id)
             | DuplicatedType SrcSpan Id
             | UndefinedTyCon SrcSpan Id
             | UndefinedTyVar SrcSpan Id
             | InvalidTypeParams SrcSpan [SType Id]
  deriving (Show)

type TypeCheckM a = StateT TyEnv MalgoM a

raiseError :: TcError -> TypeCheckM a
raiseError = error . show

-- Utilities
varmap :: Lens' TyEnv (Map Id (Type Id))
varmap f (TyEnv v t l) = fmap (\v' -> TyEnv v' t l) (f v)

tymap :: Lens' TyEnv (Map Id TymapEntry)
tymap f (TyEnv v t l) = fmap (\t' -> TyEnv v t' l) (f t)

labelmap :: Functor f => (Map Text (Type Id, Type Id) -> f (Map Text (Type Id, Type Id))) -> TyEnv -> f TyEnv
labelmap f (TyEnv v t l) = fmap (\l' -> TyEnv v t l') (f l)

lookupVar name = do
  vm <- use varmap
  case Map.lookup name vm of
    Just ty -> return ty
    Nothing -> error "unreachable(lookupVar)"

newMetaVar :: TypeCheckM (TyRef a)
newMetaVar = TyRef <$> newIORef Nothing

subst :: Type Id -> Map Id (Type Id) -> TypeCheckM (Type Id)
subst (TyVar v) env =
  case Map.lookup v env of
    Just t  -> return t
    Nothing -> return (TyVar v)
subst (TyApp (TyFun ps t) ts) env = do
  t' <- subst t (Map.fromList (zip ps ts))
  subst t' env
subst (TyApp (RecordC ls) ts) env = do
  ts' <- mapM (flip subst env) ts
  return (TyApp (RecordC ls) ts')
subst (TyApp (VariantC ls) ts) env = do
  ts' <- mapM (flip subst env) ts
  return (TyApp (VariantC ls) ts')
subst (TyApp tycon ts) env =
  TyApp tycon <$> mapM (`subst` env) ts
subst (TyMeta (TyRef r)) env = do
  r' <- readIORef r
  case r' of
    Just t  -> subst t env
    Nothing -> return $ TyMeta (TyRef r)

generalize :: Type Id -> TypeCheckM (TypeScheme Id)
generalize t = do
  rs <- nub . collectMeta <$> expand t
  vs <- forM rs $ \r -> do
    tv <- newId "a"
    writeIORef r $ Just $ TyVar tv
    return tv
  return (Forall vs t)
  where
    collectMeta (TyApp _ ts)       = concatMap collectMeta ts
    collectMeta (TyMeta (TyRef r)) = [r]
    collectMeta (TyVar _)          = []

instantiate :: TypeScheme Id -> TypeCheckM (Type Id)
instantiate (Forall vs t) = do
  ms <- mapM (const $ TyMeta <$> newMetaVar) vs
  subst t (Map.fromList (zip vs ms))

(=:=) :: TypeScheme Id -> TypeScheme Id -> TypeCheckM ()
(Forall xs t1) =:= (Forall ys t2) = do
  t2' <- subst t2 (Map.fromList (zip ys (map TyVar xs)))
  unify t1 t2'

-- | TyMetaが解決済みの場合、それを展開する
expand :: Type Id -> TypeCheckM (Type Id)
expand (TyApp (TyFun ps t) ts) =
  expand =<< subst t (Map.fromList (zip ps ts))
expand (TyApp tycon ts) = TyApp tycon <$> mapM expand ts
expand (TyMeta (TyRef r)) = do
  r' <- readIORef r
  case r' of
    Just t  -> expand t
    Nothing -> return $ TyMeta $ TyRef r
expand t = return t

unify :: Type Id -> Type Id -> TypeCheckM ()
unify (TyApp (TyFun ps t) ts) t2 = do
  t1 <- subst t (Map.fromList (zip ps ts))
  unify t1 t2
unify t1 (TyApp (TyFun ps t) ts) = do
  t2 <- subst t (Map.fromList (zip ps ts))
  unify t1 t2
unify t1@(TyApp (RecordC ls1) ts1) t2@(TyApp (RecordC ls2) ts2)
  | sort ls1 == sort ls2 = do
      let ts1' = map (view _2) $ sortOn (view _1) $ zip ls1 ts1
      let ts2' = map (view _2) $ sortOn (view _1) $ zip ls2 ts2
      mapM_ (uncurry unify) (zip ts1' ts2')
  | otherwise = raiseError $ UnifyError t1 t2
unify t1@(TyApp (VariantC ls1) ts1) t2@(TyApp (VariantC ls2) ts2)
  | sort ls1 == sort ls2 = do
      let ts1' = map (view _2) $ sortOn (view _1) $ zip ls1 ts1
      let ts2' = map (view _2) $ sortOn (view _1) $ zip ls2 ts2
      mapM_ (uncurry unify) (zip ts1' ts2')
  | otherwise = raiseError $ UnifyError t1 t2
unify (TyApp c1 ts1) (TyApp c2 ts2)
  | c1 == c2 = mapM_ (uncurry unify) (zip ts1 ts2)
unify (TyVar x) (TyVar y) | x == y = pass
unify (TyMeta (TyRef r1)) t2 = do
  r1' <- readIORef r1
  case r1' of
    Just t1 -> unify t1 t2
    Nothing -> unifyMeta r1 t2
unify t1 t2@TyMeta{} = unify t2 t1
unify t1 t2 = raiseError $ UnifyError t1 t2

unifyMeta :: IORef (Maybe (Type Id)) -> Type Id -> TypeCheckM ()
unifyMeta r1 (TyApp (TyFun ps t) ts) = do
  t2 <- subst t (Map.fromList $ zip ps ts)
  unifyMeta r1 t2
unifyMeta r1 (TyMeta (TyRef r2)) = do
  r2' <- readIORef r2
  whenJust r2' (unifyMeta r1)
unifyMeta r1 t2 | occur r1 t2 = raiseError $ UnifyError (TyMeta (TyRef r1)) t2
                | otherwise = writeIORef r1 (Just t2)

occur :: IORef (Maybe (Type a)) -> Type a -> Bool
occur r (TyApp _ ts) = any (occur r) ts
occur _ (TyVar _) = False
occur r1 (TyMeta (TyRef r2)) | r1 == r2 = True
                             | otherwise = False

-- Functions
typeCheck :: Rename.RnEnv -> [Decl Id] -> MalgoM TyEnv
typeCheck rnEnv ds = flip execStateT (initTyEnv rnEnv) $ do
  mapM_ checkDecl ds

transTy :: SType Id -> TypeCheckM (Type Id)
transTy (STyVar ss name) = do
  tm <- use tymap
  case Map.lookup name tm of
    Just (Type t) -> return t
    _             -> raiseError (UndefinedTyVar ss name)
transTy (STyApp ss (SimpleC _ name) args) = do
  tm <- use tymap
  args' <- mapM transTy args
  case Map.lookup name tm of
    Just (TyCon tycon) -> return $ TyApp tycon args'
    _                  -> raiseError (UndefinedTyCon ss name)
transTy (STyApp _ (SRecordC _ xs) []) = do
  t <- TyMeta <$> newMetaVar
  ts <- mapM (uncurry $ transFieldTy t) xs
  let t' = TyApp (RecordC (map (view _1) xs)) ts
  unify t t'
  return t
transTy (STyApp _ (SVariantC _ xs) []) = do
  t <- TyMeta <$> newMetaVar
  ts <- mapM (uncurry $ transFieldTy t) xs
  let t' = TyApp (VariantC (map (view _1) xs)) ts
  unify t t'
  return t
transTy (STyApp ss _ ts) = raiseError $ InvalidTypeParams ss ts

transFieldTy :: Type Id -> Text -> SType Id -> TypeCheckM (Type Id)
transFieldTy containerTy label ty = do
  lm <- use labelmap
  ty' <- transTy ty
  case Map.lookup label lm of
    Just (containerTy', elemTy) -> do
      unify containerTy containerTy'
      unify ty' elemTy
    Nothing -> do
      modify (over labelmap (Map.singleton label (containerTy, ty') <>))
  return ty'

checkDecl :: Decl Id -> TypeCheckM ()
checkDecl (TypeDef ss name [] ty) = do
  tm <- use tymap
  whenJust (Map.lookup name tm) $ \_ -> raiseError $ DuplicatedType ss name
  ty' <- transTy ty
  modify (over tymap (Map.singleton name (Type ty') <>))
checkDecl (TypeDef ss name ps ty) = do
  tm <- use tymap
  whenJust (Map.lookup name tm) $ \_ -> raiseError $ DuplicatedType ss name
  modify (over tymap (Map.fromList
                      (zip ps (map (Type . TyVar) ps)) <>))
  ty' <- transTy ty
  modify (over tymap (Map.singleton name (TyCon $ TyFun ps ty') <>))
checkDecl (ScAnn _ name ty) = do
  ty' <- transTy ty
  vm <- use varmap
  whenJust (Map.lookup name vm) $ \inferedType -> do
    unify inferedType ty'
  modify (over varmap (Map.singleton name ty' <>))
checkDecl (ScDef _ name params expr) = do
  paramTypes <- mapM (const $ TyMeta <$> newMetaVar) params
  modify (over varmap (Map.fromList (zip params paramTypes) <>))

  metaExprType <- TyMeta <$> newMetaVar

  let ty = makeType paramTypes metaExprType

  vm <- use varmap
  whenJust (Map.lookup name vm) $ \annType ->
    unify annType ty

  modify (over varmap (Map.singleton name ty <>))

  exprType <- checkExpr expr
  unify metaExprType exprType

  where
    makeType [] ret = ret
    makeType (x:xs) ret =
      foldr' (\t1 t2 -> TyApp ArrowC [t1, t2]) x (xs <> [ret])

checkExpr :: Expr Id -> TypeCheckM (Type Id)
checkExpr (Var _ name) = lookupVar name
checkExpr (Literal _ lit) = checkLiteral lit
  where
    checkLiteral (Int _)   = return $ TyApp (IntC 64) []
    checkLiteral (Float _) = return $ TyApp Float32C []
    checkLiteral (Bool _)  = return $ TyApp (IntC 1) []
    checkLiteral (Char _)  = return $ TyApp (IntC 8) []
