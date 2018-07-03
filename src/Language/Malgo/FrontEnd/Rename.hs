{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
module Language.Malgo.FrontEnd.Rename ( rename ) where

import           Control.Monad.Except
import           Data.Text.Prettyprint.Doc
import           Language.Malgo.ID         hiding (newID)
import           Language.Malgo.IR.Syntax  hiding (info)
import           Language.Malgo.Monad
import           Language.Malgo.Prelude    (Info)
import           RIO
import qualified RIO.Map                   as Map

type RnEnv = Map.Map Text RawID

rename :: Expr Text -> RIO MalgoApp (Maybe (Expr RawID))
rename e = do
  e' <- runExceptT $ runReaderT (renameExpr e) Map.empty
  case e' of
    Right x -> return (Just x)
    Left x -> do
      logError (displayShow x)
      return Nothing

type RenameM ann a = ReaderT RnEnv (ExceptT (Doc ann) (RIO MalgoApp)) a

addKnowns :: [(Text, RawID)] -> RenameM ann a -> RenameM ann a
addKnowns kvs m =
  local (Map.fromList kvs <>)  m

getID :: Info -> Text -> RenameM ann RawID
getID info name = do
  k <- ask
  case Map.lookup name k of
    Just x -> return x
    Nothing -> throwError ("error(rename):" <+> pretty info <+> pretty name <+> "is not defined")

newID :: Text -> RenameM ann RawID
newID name = do
  u <- lift $ lift newUniq'
  return (ID name u ())

renameExpr :: Expr Text -> RenameM ann (Expr RawID)
renameExpr (Var info name) = Var info <$> getID info name
renameExpr (Int info x) = return $ Int info x
renameExpr (Float info x) = return $ Float info x
renameExpr (Bool info x) = return $ Bool info x
renameExpr (Char info x) = return $ Char info x
renameExpr (String info x) = return $ String info x
renameExpr (Unit info) = return $ Unit info
renameExpr (Tuple info xs) = Tuple info <$> mapM renameExpr xs
renameExpr (TupleAccess info e i) = TupleAccess info <$> renameExpr e <*> pure i
renameExpr (Fn info params body) = do
  paramIDs <- mapM (newID . fst) params
  addKnowns (zip (map fst params) paramIDs) $ do
    params' <- mapM (\(n, t) -> (,) <$> getID info n <*> pure t) params
    body' <- renameExpr body
    return $ Fn info params' body'
renameExpr (Call info fn args) =
  Call info <$> renameExpr fn <*> mapM renameExpr args
renameExpr (Seq info e1 e2) =
  Seq info <$> renameExpr e1 <*> renameExpr e2
renameExpr (Let info decls e) = do
  declIDs <- mapM (newID . getName) decls
  addKnowns (zip (map getName decls) declIDs) $ do
    decls' <- mapM renameDecl decls
    e' <- renameExpr e
    pure (Let info decls' e')
  where getName (ExDec _ name _ _)    = name
        getName (FunDec _ name _ _ _) = name
        getName (ValDec _ name _ _)   = name
renameExpr (If info c t f) =
  If info <$> renameExpr c <*> renameExpr t <*> renameExpr f
renameExpr (BinOp info op x y) = BinOp info op <$> renameExpr x <*> renameExpr y

renameDecl :: Decl Text -> RenameM ann (Decl RawID)
renameDecl (ValDec info name typ val) = do
  val' <- renameExpr val
  name' <- getID info name
  return (ValDec info name' typ val')
renameDecl (FunDec info fn params retty body) = do
  fn' <- getID info fn
  paramIDs <- mapM (newID . fst) params
  addKnowns (zip (map fst params) paramIDs) $ do
    params' <- mapM (\(n, t) -> (,) <$> getID info n <*> pure t) params
    body' <- renameExpr body
    return (FunDec info fn' params' retty body')
renameDecl (ExDec info name typ orig) = do
  name' <- getID info name
  return $ ExDec info name' typ orig