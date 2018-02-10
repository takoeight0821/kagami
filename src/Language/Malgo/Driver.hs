{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}

module Language.Malgo.Driver where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State.Strict
import           Data.Semigroup
import qualified Data.Text.Lazy.IO          as Text
import qualified Language.Malgo.Beta        as Beta
import qualified Language.Malgo.Closure     as Closure
import qualified Language.Malgo.CodeGen     as CodeGen
import qualified Language.Malgo.Eval        as Eval
import qualified Language.Malgo.Flatten     as Flatten
import qualified Language.Malgo.KNormal     as KNormal
import           Language.Malgo.MIR
import qualified Language.Malgo.Rename      as Rename
import qualified Language.Malgo.Syntax      as Syntax
import qualified Language.Malgo.TypeCheck   as TypeCheck
import qualified Language.Malgo.Unused      as Unused
import           Language.Malgo.Utils
import           LLVM.Pretty
import           Options.Applicative

parseOpt :: IO Opt
parseOpt = execParser $
  info ((Opt
          <$> strArgument (metavar "(FILENAME)" <> help "Source file" <> action "file")
          <*> switch (long "dump-parsed")
          <*> switch (long "dump-renamed")
          <*> switch (long "dump-typed")
          <*> switch (long "dump-hir")
          <*> switch (long "dump-beta")
          <*> switch (long "dump-flatten")
          <*> switch (long "dump-closure"))
          <*> switch (long "compile-only")
          <*> switch (long "not-remove-unused")
          <*> switch (long "dump-llvm")
         <**> helper)
  (fullDesc
    <> progDesc "A interpreter of malgo"
    <> header "malgo - a toy programming language")

compile ::
  Syntax.Expr Name -> Opt -> IO (Program TypeCheck.TypedID)
compile ast opt = do
  when (_dumpParsed opt) $
    liftIO . print $ pretty ast
  (renamed, s1) <- run _dumpRenamed (Rename.rename ast) 0
  (typed, s2) <- run _dumpTyped (TypeCheck.typeCheck renamed) s1
  (knormal, s3) <- run _dumpHIR (KNormal.knormal typed) s2
  (beta, s4) <- run _dumpBeta (Beta.betaTrans knormal) s3
  when (_dumpFlatten opt) $
    liftIO (print $ pretty (Flatten.flatten beta))
  (cls, _) <- run (const False) (Closure.conv beta) s4
  let cls' = if _notRemoveUnused opt
             then cls
             else Unused.remove cls
  when (_dumpClosure opt) $
    liftIO . print $ pretty cls'
  when (_dumpLLVM opt) $ do
    let llvm = CodeGen.dumpCodeGen (CodeGen.genProgram cls')
    liftIO (mapM_ (Text.putStrLn . ppll) llvm)
  return cls'
  where run key m u =
          runMalgoT m u >>= \(x', u') ->
                              do when (key opt) $
                                   liftIO . print $ pretty x'
                                 return (x', u')

eval :: Program TypeCheck.TypedID -> IO Eval.Value
eval prog = fst <$> runMalgoT (Eval.eval prog) 0