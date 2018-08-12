{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
module Language.Malgo.Driver where

import           Data.Outputable
import qualified Language.Malgo.BackEnd.LLVM                 as LLVM
import qualified Language.Malgo.FrontEnd.Rename              as Rename
import qualified Language.Malgo.FrontEnd.TypeCheck           as TypeCheck
import           Language.Malgo.ID
import qualified Language.Malgo.IR.IR                        as IR
import qualified Language.Malgo.IR.Syntax                    as Syntax
import qualified Language.Malgo.MiddleEnd.BasicLint          as BasicLint
import qualified Language.Malgo.MiddleEnd.Closure.Preprocess as Closure
import qualified Language.Malgo.MiddleEnd.Closure.Trans      as Closure
import qualified Language.Malgo.MiddleEnd.MutRec             as MutRec
import qualified Language.Malgo.MiddleEnd.TransToIR          as TransToIR
import           Language.Malgo.Monad                        as M
import           Language.Malgo.Pretty
import qualified LLVM.AST                                    as L
import           Options.Applicative
import           Universum

parseOpt :: IO Opt
parseOpt = execParser $
  info ((Opt
          <$> strArgument (metavar "(FILENAME)" <> help "Source file" <> action "file")
          <*> switch (long "dump-parsed")
          <*> switch (long "dump-renamed")
          <*> switch (long "dump-typed")
          <*> switch (long "dump-knormal")
          <*> switch (long "dump-type-table")
          <*> switch (long "dump-closure"))
          <*> switch (long "debug-mode")
         <**> helper) (fullDesc
    <> progDesc "malgo"
    <> header "malgo - a toy programming language")

dump :: (MonadReader MalgoEnv m, Outputable a, MonadIO m, Pretty a) => a -> m ()
dump x = do
  opt <- asks maOption
  if _isDebugMode opt
  then print $ ppr x
  else print $ pPrint x

frontend :: Syntax.Expr Text -> MalgoM (Syntax.Expr TypedID)
frontend ast = do
  opt <- asks maOption
  when (_dumpParsed opt) $
    dump ast
  renamed <- Rename.rename ast
  when (_dumpRenamed opt) $
    dump renamed
  typed <- TypeCheck.typeCheck renamed
  when (_dumpTyped opt) $
    dump typed
  return typed

middleend :: Syntax.Expr TypedID -> MalgoM (IR.Program (ID IR.MType))
middleend ast = do
  opt <- asks maOption
  ir <- TransToIR.trans ast
  when (_dumpKNormal opt) $
    dump $ IR.flattenExpr ir
  case BasicLint.lint ir of
    Right _  -> pass
    Left mes -> error $ show mes
  M.UniqSupply u <- M.maUniqSupply <$> ask
  writeIORef u 0
  ir' <- MutRec.remove ir
  case BasicLint.lint ir' of
    Right _  -> pass
    Left mes -> error $ show mes
  case MutRec.lint ir' of
    Right _  -> pass
    Left mes -> error $ show mes

  let (_, tt) = Closure.divideTypeFromExpr ir'
  when (_dumpTypeTable opt) $
    print $ ppr $ toPairs tt

  ir'' <- Closure.trans ir'
  when (_dumpClosure opt) $
    dump $ IR.flattenProgram ir''
  case BasicLint.runLint (BasicLint.lintProgram ir'') of
    Right _  -> pass
    Left mes -> error $ show mes

  return ir''

backend :: MonadIO m => Text -> IR.Program (ID IR.MType) -> m L.Module
backend filename ir = do
  defs <- LLVM.dumpLLVM (LLVM.genProgram ir)
  return $ L.defaultModule { L.moduleName = fromString $ toString filename
                           , L.moduleSourceFileName = fromString $ toString filename
                           , L.moduleDefinitions = defs
                           }

compile :: MonadIO m => Text -> Syntax.Expr Text -> UniqSupply -> Opt -> m L.Module
compile filename ast = M.runMalgo $ do
  typed <- frontend ast
  ir <- middleend typed
  backend filename ir
