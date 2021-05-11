{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Malgo.Driver (compile, compileFromAST) where

import Colog (Message, WithLog, log, pattern I)
import Colog.Actions (richMessageAction)
import Data.Maybe (fromJust)
import qualified Data.Text.IO as T
import Koriel.Core.CodeGen (codeGen)
import Koriel.Core.Flat (flat)
import Koriel.Core.LambdaLift (lambdalift)
import Koriel.Core.Lint (lintProgram, runLint)
import Koriel.Core.Optimize (optimizeProgram)
import Koriel.Core.Syntax
import Koriel.MonadUniq
import Koriel.Pretty
import Language.Malgo.Desugar.Pass (desugar)
import Language.Malgo.Interface (buildInterface, loadInterface, storeInterface)
import Language.Malgo.Parser (parseMalgo)
import Language.Malgo.Prelude
import Language.Malgo.Refine.Pass (refine)
import Language.Malgo.Rename.Pass (rename)
import qualified Language.Malgo.Rename.RnEnv as RnEnv
import qualified Language.Malgo.Syntax as Syntax
import Language.Malgo.Syntax.Extension
import qualified Language.Malgo.TypeCheck.Pass as TypeCheck
import qualified Language.Malgo.TypeCheck.TcEnv as TcEnv
import qualified Language.Malgo.TypeRep.Static as Static
import Text.Megaparsec
  ( errorBundlePretty,
  )

-- |
-- dumpHoge系のフラグによるダンプ出力を行うコンビネータ
--
-- 引数 m のアクションの返り値をpPrintしてstderrに吐く
withDump ::
  (WithLog env Message m, MonadIO m, Pretty a) =>
  -- | dumpHoge系のフラグの値
  Bool ->
  Doc ->
  m a ->
  m a
withDump isDump label m = do
  result <- m
  when isDump $ log I $ fromString $ show $ label $$ pPrint result
  pure result

executingMalgoM :: Opt -> MalgoM a -> IO ()
executingMalgoM opt m = void $ runUniqT (runReaderT (unMalgoM m) MalgoEnv {_malgoOpt = opt, _malgoLogAction = richMessageAction}) (UniqSupply 0)

compileFromAST :: Syntax.Module (Malgo 'Parse) -> Opt -> IO ()
compileFromAST parsedAst opt = executingMalgoM opt do
  when (dumpParsed opt) $ log I $ fromString $ show $ "=== PARSED ===" $$ pPrint parsedAst
  rnEnv <- RnEnv.genBuiltinRnEnv
  (renamedAst, rnState) <- rename rnEnv parsedAst
  when (dumpRenamed opt) $ log I $ fromString $ show $ "=== RENAME ===" $$ pPrint (renamedAst, rnState)
  (typedAst, tcEnv) <- withDump (dumpTyped opt) "=== TYPE CHECK ===" $ TypeCheck.typeCheck rnEnv renamedAst
  when (dumpTyped opt) $ log I $ fromString $ show $ "=== TYPE CHECK ===" $$ pPrint (typedAst, tcEnv)
  refinedAst <- refine typedAst
  let varEnv = fromJust $ traverse (traverse Static.safeToType) $ tcEnv ^. TcEnv.varEnv
  let typeEnv = fromJust $ traverse (traverse Static.safeToType) $ tcEnv ^. TcEnv.typeEnv
  let fieldEnv = fromJust $ traverse (traverse Static.safeToType) $ tcEnv ^. TcEnv.fieldEnv
  (dsEnv, core) <- withDump (dumpDesugar opt) "=== DESUGAR ===" $ desugar varEnv typeEnv fieldEnv (tcEnv ^. TcEnv.rnEnv) refinedAst
  when (dumpDesugar opt) $ log I $ fromString $ show $ "=== DESUGAR ===" $$ pPrint (dsEnv, core)
  let inf = buildInterface rnState dsEnv
  storeInterface inf
  when (debugMode opt) $ do
    inf <- loadInterface (Syntax._moduleName typedAst)
    log I $ fromString $ show $ "=== INTERFACE ===" $$ pPrint inf
  runLint $ lintProgram core
  coreOpt <- if noOptimize opt then pure core else optimizeProgram (inlineSize opt) core
  when (dumpDesugar opt && not (noOptimize opt)) $ log I $ fromString $ show $ "=== OPTIMIZE ===" $$ pPrint (over appProgram flat coreOpt)
  runLint $ lintProgram coreOpt
  coreLL <- if noLambdaLift opt then pure coreOpt else lambdalift coreOpt
  when (dumpDesugar opt && not (noLambdaLift opt)) $ log I $ fromString $ show $ "=== LAMBDALIFT ===" $$ pPrint (over appProgram flat coreLL)
  coreLLOpt <- if noOptimize opt then pure coreLL else optimizeProgram (inlineSize opt) coreLL
  when (dumpDesugar opt && not (noLambdaLift opt) && not (noOptimize opt)) $ log I $ fromString $ show $ "=== LAMBDALIFT OPTIMIZE ===" $$ pPrint (over appProgram flat coreLLOpt)
  codeGen (srcName opt) (dstName opt) coreLLOpt

-- | .mlgから.llへのコンパイル
compile :: Opt -> IO ()
compile opt = do
  src <- T.readFile (srcName opt)
  parsedAst <- case parseMalgo (srcName opt) src of
    Right x -> pure x
    Left err -> error $ errorBundlePretty err
  compileFromAST parsedAst opt
