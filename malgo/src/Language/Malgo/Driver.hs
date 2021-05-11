{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Malgo.Driver (compile, compileFromAST) where

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
import System.IO
  ( hPrint,
    hPutStrLn,
    stderr,
  )
import Text.Megaparsec
  ( errorBundlePretty,
  )

-- |
-- dumpHoge系のフラグによるダンプ出力を行うコンビネータ
--
-- 引数 m のアクションの返り値をpPrintしてstderrに吐く
withDump ::
  (MonadIO m, Pretty a) =>
  -- | dumpHoge系のフラグの値
  Bool ->
  String ->
  m a ->
  m a
withDump isDump label m = do
  result <- m
  when isDump $ liftIO do
    hPutStrLn stderr label
    hPrint stderr $ pPrint result
  pure result

executingMalgoM :: Opt -> MalgoM a -> IO ()
executingMalgoM opt m = void $ runReaderT (runUniqT (unMalgoM m) (UniqSupply 0)) MalgoEnv {_malgoOpt = opt}

compileFromAST :: Syntax.Module (Malgo 'Parse) -> Opt -> IO ()
compileFromAST parsedAst opt = executingMalgoM opt do
  when (dumpParsed opt) $ liftIO do
    hPutStrLn stderr "=== PARSED ==="
    hPrint stderr $ pPrint parsedAst
  rnEnv <- RnEnv.genBuiltinRnEnv
  (renamedAst, rnState) <- withDump (dumpRenamed opt) "=== RENAME ===" $ rename rnEnv parsedAst
  (typedAst, tcEnv) <- withDump (dumpTyped opt) "=== TYPE CHECK ===" $ TypeCheck.typeCheck rnEnv renamedAst
  refinedAst <- refine typedAst
  let varEnv = fromJust $ traverse (traverse Static.safeToType) $ tcEnv ^. TcEnv.varEnv
  let typeEnv = fromJust $ traverse (traverse Static.safeToType) $ tcEnv ^. TcEnv.typeEnv
  let fieldEnv = fromJust $ traverse (traverse Static.safeToType) $ tcEnv ^. TcEnv.fieldEnv
  (dsEnv, core) <- withDump (dumpDesugar opt) "=== DESUGAR ===" $ desugar varEnv typeEnv fieldEnv (tcEnv ^. TcEnv.rnEnv) refinedAst
  let inf = buildInterface rnState dsEnv
  storeInterface inf
  when (debugMode opt) $ do
    inf <- loadInterface (Syntax._moduleName typedAst)
    liftIO $ do
      hPutStrLn stderr "=== INTERFACE ==="
      hPutStrLn stderr $ renderStyle (style {lineLength = 120}) $ pPrint inf
  runLint $ lintProgram core
  coreOpt <- if noOptimize opt then pure core else optimizeProgram (inlineSize opt) core
  when (dumpDesugar opt && not (noOptimize opt)) $
    liftIO $ do
      hPutStrLn stderr "=== OPTIMIZE ==="
      hPrint stderr $ pPrint $ over appProgram flat coreOpt
  runLint $ lintProgram coreOpt
  coreLL <- if noLambdaLift opt then pure coreOpt else lambdalift coreOpt
  when (dumpDesugar opt && not (noLambdaLift opt)) $
    liftIO $ do
      hPutStrLn stderr "=== LAMBDALIFT ==="
      hPrint stderr $ pPrint $ over appProgram flat coreLL
  coreLLOpt <- if noOptimize opt then pure coreLL else optimizeProgram (inlineSize opt) coreLL
  when (dumpDesugar opt && not (noLambdaLift opt) && not (noOptimize opt)) $
    liftIO $ do
      hPutStrLn stderr "=== LAMBDALIFT OPTIMIZE ==="
      hPrint stderr $ pPrint $ over appProgram flat coreLLOpt

  codeGen (srcName opt) (dstName opt) coreLLOpt

-- | .mlgから.llへのコンパイル
compile :: Opt -> IO ()
compile opt = do
  src <- T.readFile (srcName opt)
  parsedAst <- case parseMalgo (srcName opt) src of
    Right x -> pure x
    Left err -> error $ errorBundlePretty err
  when (dumpParsed opt) $ do
    hPutStrLn stderr "=== PARSE ==="
    hPrint stderr $ pPrint parsedAst
  compileFromAST parsedAst opt
