{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
module Language.Malgo.FrontEnd.Typing.Infer (Typing) where

import           Language.Malgo.FrontEnd.Info
import           Language.Malgo.FrontEnd.Typing.Constraint
import           Language.Malgo.FrontEnd.Typing.Subst
import           Language.Malgo.ID
import           Language.Malgo.IR.Syntax                  hiding (info)
import qualified Language.Malgo.IR.Syntax                  as Syntax
import           Language.Malgo.Monad
import           Language.Malgo.Pass
import           Language.Malgo.Pretty                     hiding (first)
import           Language.Malgo.TypeRep.Type
import           Relude                                    hiding (Constraint,
                                                            Type)
import           Relude.Extra.Map

data Typing

instance Pass Typing (Expr (ID ())) (Expr (ID Type)) where
  isDump = dumpTyped
  trans e = evaluatingStateT mempty $ do
    (cs, _) <- typingExpr e
    subst <- catchUnifyError (Syntax.info e) Nothing $ solve cs
    env <- gets (defaulting . apply subst)
    mapM (updateID env) e

defaulting :: Substitutable a => a -> a
defaulting t = apply (Subst $ fromList $ zip (toList $ ftv t) (repeat TyInt)) t


type Env = IDMap () (ID Type)

type InferM a = StateT Env MalgoM a

throw :: Info -> Doc -> InferM a
throw info mes = errorDoc $ "error(typing):" <+> pPrint info $+$ mes

catchUnifyError :: Info -> Maybe (ID ()) -> Either UnifyError a -> InferM a
catchUnifyError i n (Left (MismatchConstructor c1 c2)) =
  throw i $ "mismatch constructor" <+> pPrint c1 <+> pPrint c2
  $+$ case n of
        Nothing -> mempty
        Just n' -> "on" <+> pPrint n'
catchUnifyError i n (Left (MismatchLength ts1 ts2)) =
  throw i $ "mismatch length" <+> pPrint ts1 <+> pPrint ts2
  $+$ case n of
        Nothing -> mempty
        Just n' -> "on" <+> pPrint n'
catchUnifyError i n (Left (InfinitType var ty)) =
  throw i $ "infinit type" <+> pPrint var <+> pPrint ty
  $+$ case n of
        Nothing -> mempty
        Just n' -> "on" <+> pPrint n'
catchUnifyError _ _ (Right a) = pure a

updateID :: Env -> ID () -> InferM (ID Type)
updateID env x = case lookup x env of
  Nothing -> errorDoc $ "error(updateID):" <+> pPrint x
  Just y  -> return y

newTyMeta :: InferM Type
newTyMeta = TyMeta <$> newUniq

defineVar :: Info -> ID () -> Type -> [Constraint] -> InferM ()
defineVar i x t cs = do
  sub <- catchUnifyError i (Just x) $ solve cs
  x' <- newID (apply sub t) (_idName x)
  modify (insert x x')

lookupVar :: ID () -> InferM Type
lookupVar x = do
  env <- get
  case lookup x env of
    Nothing -> errorDoc $ "error(lookupVar):" <+> pPrint x
    Just y  -> pure $ typeOf y

typingExpr :: Expr (ID ()) -> InferM ([Constraint], Type)
typingExpr (Var i x) = do
  env <- get
  case lookup x env of
    Nothing -> throw i $ "unbound variable:" <+> pPrint x $+$ "Env:" <+> pPrint (toList env)
    Just y  -> return ([], _idMeta y)
typingExpr Int{} = return ([], TyInt)
typingExpr Float{} = return ([], TyFloat)
typingExpr Bool{} = return ([], TyBool)
typingExpr Char{} = return ([], TyChar)
typingExpr String{} = return ([], TyString)
typingExpr Unit{} = return ([], TyTuple [])
typingExpr (Tuple _ xs) = do
  (cs, ts) <- first mconcat <$> mapAndUnzipM typingExpr xs
  return (cs, TyTuple ts)
typingExpr (TupleAccess _ e _) = do
  -- FIXME: 正しく型付けする
  (cs, _) <- typingExpr e
  t <- newTyMeta
  return (cs, t)
typingExpr (MakeArray _ ty sizeNode) = do
  (cs, sizeTy) <- typingExpr sizeNode
  return (TyInt :~ sizeTy : cs, TyArray ty)
typingExpr (ArrayRead _ arr _) = do
  (cs, arrTy) <- typingExpr arr
  resultTy <- newTyMeta
  return (TyArray resultTy :~ arrTy : cs, resultTy)
typingExpr (ArrayWrite _ arr ix val) = do
  (cs1, arrTy) <- typingExpr arr
  (cs2, ixTy) <- typingExpr ix
  (cs3, valTy) <- typingExpr val
  return (ixTy :~ TyInt : arrTy :~ TyArray valTy : cs3 <> cs2 <> cs1, TyTuple [])
typingExpr (Call _ fn args) = do
  (cs1, fnTy) <- typingExpr fn
  (cs2, argTypes) <- first mconcat <$> mapAndUnzipM typingExpr args
  retTy <- newTyMeta
  return (TyFun argTypes retTy :~ fnTy : cs1 <> cs2, retTy)
typingExpr (Fn i params body) = do
  paramTypes <- mapM (\case
                         (_, Just t) -> pure t
                         (_, Nothing) -> newTyMeta) params
  mapM_ (\((p, _), t) -> defineVar i p t []) (zip params paramTypes)
  (cs, t) <- typingExpr body
  return (cs, TyFun paramTypes t)
typingExpr (Seq _ e1 e2) = do
  (cs1, _) <- typingExpr e1
  (cs2, t) <- typingExpr e2
  return (cs1 <> cs2, t)
typingExpr (Let _ [ValDec i name mtyp val] body) = do
  (cs1, valType) <- typingExpr val
  let cs2 = case mtyp of
              Just typ -> valType :~ typ : cs1
              Nothing  -> cs1
  defineVar i name valType cs2
  (cs3, t) <- typingExpr body
  return (cs1 <> cs2 <> cs3, t)
typingExpr (Let _ [ExDec i name typ _] body) = do
  defineVar i name typ []
  (cs, t) <- typingExpr body
  return (cs, t)
typingExpr (Let i fs e) = do
  mapM_ prepare fs
  cs1 <- concat <$> mapM typingFunDec fs
  (cs2, t) <- typingExpr e
  return (cs1 <> cs2, t)
  where
    prepare :: Decl (ID ()) -> InferM ()
    prepare (FunDec i' f _ _ _) = do
      v <- newTyMeta
      defineVar i' f v []
    prepare _                   = errorDoc $ "error(prepare):" <+> pPrint i
    typingFunDec (FunDec i' f params retty body) = do
      paramTypes <- mapM (\case
                             (_, Just t) -> pure t
                             (_, Nothing) -> newTyMeta) params
      mapM_ (\((p, _), t) -> defineVar i p t []) (zip params paramTypes)
      (cs1, t) <- typingExpr body
      tv <- lookupVar f
      let cs = tv :~ TyFun paramTypes retty : t :~ retty : cs1
      defineVar i' f tv cs
      return cs
    typingFunDec x = errorDoc $ "error(typingFunDec):" <+> pPrint x
typingExpr (If _ c t f) = do
  (cs1, ct) <- typingExpr c
  (cs2, tt) <- typingExpr t
  (cs3, ft) <- typingExpr f
  return (ct :~ TyBool : tt :~ ft : cs1 <> cs2 <> cs3, ft)
typingExpr (BinOp _ op x y) = do
  opType <- typingOp op
  (cs1, xt) <- typingExpr x
  (cs2, yt) <- typingExpr y
  resultType <- newTyMeta
  return (opType :~ TyFun [xt, yt] resultType : cs1 <> cs2, resultType)
  where
    typingOp Add  = pure $ TyFun [TyInt, TyInt] TyInt
    typingOp Sub  = pure $ TyFun [TyInt, TyInt] TyInt
    typingOp Mul  = pure $ TyFun [TyInt, TyInt] TyInt
    typingOp Div  = pure $ TyFun [TyInt, TyInt] TyInt
    typingOp Mod  = pure $ TyFun [TyInt, TyInt] TyInt
    typingOp FAdd = pure $ TyFun [TyFloat, TyFloat] TyFloat
    typingOp FSub = pure $ TyFun [TyFloat, TyFloat] TyFloat
    typingOp FMul = pure $ TyFun [TyFloat, TyFloat] TyFloat
    typingOp FDiv = pure $ TyFun [TyFloat, TyFloat] TyFloat
    typingOp Eq   = newTyMeta >>= \a -> pure $ TyFun [a, a] TyBool
    typingOp Neq  = newTyMeta >>= \a -> pure $ TyFun [a, a] TyBool
    typingOp Lt   = newTyMeta >>= \a -> pure $ TyFun [a, a] TyBool
    typingOp Gt   = newTyMeta >>= \a -> pure $ TyFun [a, a] TyBool
    typingOp Le   = newTyMeta >>= \a -> pure $ TyFun [a, a] TyBool
    typingOp Ge   = newTyMeta >>= \a -> pure $ TyFun [a, a] TyBool
    typingOp And  = pure $ TyFun [TyBool, TyBool] TyBool
    typingOp Or   = pure $ TyFun [TyBool, TyBool] TyBool
