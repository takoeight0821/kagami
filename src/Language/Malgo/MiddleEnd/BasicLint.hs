{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
module Language.Malgo.MiddleEnd.BasicLint (lint, runLint, lintExpr, lintProgram) where

import           Control.Monad.Except  (MonadError, runExcept, throwError)
import           Language.Malgo.ID
import           Language.Malgo.IR.IR
import           Language.Malgo.Pretty
import           Universum

lint :: Expr (ID MType) -> Either Doc MType
lint expr = runExcept $ evalStateT (lintExpr expr) []

runLint :: StateT [ID MType] (ExceptT Doc Identity) a -> Either Doc a
runLint = runExcept . flip evalStateT []

defined :: (MonadState [ID MType] m, MonadError Doc m) => ID MType -> m ()
defined a =
  unlessM (elem a <$> get)
  (throwError $ pPrint a <+> "is not defined")

notDefined :: (MonadState [ID MType] m, MonadError Doc m) => ID MType -> m ()
notDefined a =
  unlessM (notElem a <$> get)
  (throwError $ pPrint a <+> "is already defined")

lintExpr :: (MonadState [ID MType] m, MonadError Doc m) => Expr (ID MType) -> m MType
lintExpr (Let name val body) = do
  notDefined name
  val' <- lintExpr val
  if mTypeOf name == val'
    then modify (name:) >> lintExpr body
    else throwError $ pPrint val <+> "cannot assign to:" <+> (pPrint name <> ":" <> pPrint (mTypeOf name))
lintExpr e@(Apply f args) = do
  mapM_ defined (f:args)
  paramtys <- getParamtys
  if paramtys /= argtys
    then throwError ("expected:" <+> pPrint paramtys <> ","
                     $+$ "actual:" <+> pPrint argtys
                     $+$ "code:" <+> pPrint e)
    else return (mTypeOf e)
  where fty = mTypeOf f
        argtys = map mTypeOf args
        getParamtys =
          case fty of
            FunctionTy _ ts -> return ts
            t -> throwError $ pPrint t <+> ("is not applieable: " <> parens (pPrint e))
lintExpr (Access e is) =
  defined e >> accessMType (mTypeOf e) is
lintExpr (If c t f)
  | mTypeOf c == IntTy 1 = do
      defined c
      t' <- lintExpr t
      f' <- lintExpr f
      if t' == f'
        then return t'
        else throwError $ pPrint t <+> "must be typed as:" <+> pPrint f'
  | otherwise = throwError $ pPrint c <+> "must be typed as: i1"
lintExpr (Var a) =
  defined a >> return (mTypeOf a)
lintExpr e@(Tuple xs) =
  mapM_ defined xs >> return (mTypeOf e)
lintExpr (LetRec fundecs body) = do
  modify (map (view _1) fundecs ++)
  mapM_ lintFunDec fundecs
  lintExpr body
lintExpr (Cast ty a) =
  defined a >> return ty
lintExpr e = return $ mTypeOf e

lintFunDec :: (MonadState [ID MType] m, MonadError Doc m) => (ID MType, [ID MType], Expr (ID MType)) -> m ()
lintFunDec (_, params, fbody) =
  modify (params <>) >> void (lintExpr fbody)

lintDefn :: (MonadState [ID MType] m, MonadError Doc m) => Defn (ID MType) -> m ()
lintDefn (DefFun _ params fbody) =
  modify (params ++) >> void (lintExpr fbody)

lintProgram :: (MonadState [ID MType] m, MonadError Doc m) => Program (ID MType) -> m ()
lintProgram (Program _ xs) = do
  modify (map (\(DefFun f _ _) -> f) xs ++)
  mapM_ lintDefn xs
