{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Griff.Prelude
  ( module Koriel.Prelude,
    MonadGriff (..),
    GriffM (..),
    errorOn,
    Opt (..),
    parseOpt,
  )
where

import Control.Monad.Fix (MonadFix)
import Koriel.MonadUniq
import Koriel.Prelude
import Koriel.Pretty
import Options.Applicative
import System.FilePath.Lens
import Text.Megaparsec.Pos (SourcePos (sourceLine), unPos)

newtype GriffM a = GriffM {unGriffM :: ReaderT Opt IO a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadFix, MonadFail)

class Monad m => MonadGriff m where
  getOpt :: m Opt
  default getOpt :: (MonadTrans t, MonadGriff m1, m ~ t m1) => m Opt
  getOpt = lift getOpt

viewLine :: (MonadGriff m, MonadIO m) => Int -> m String
viewLine linum = do
  srcFileName <- srcName <$> getOpt
  s <- liftIO $ readFile srcFileName
  pure $ lines s !! (linum - 1)

errorOn :: (MonadGriff m, MonadIO m) => SourcePos -> Doc -> m a
errorOn pos x = do
  line <- viewLine (unPos $ sourceLine pos)
  errorDoc $
    "error on" <+> pPrint pos <> ":" $+$ nest 2 x
      $+$ pPrint (unPos $ sourceLine pos) <+> text line

instance MonadGriff GriffM where
  getOpt = GriffM ask

instance MonadGriff m => MonadGriff (ReaderT r m)

instance MonadGriff m => MonadGriff (ExceptT e m)

instance MonadGriff m => MonadGriff (StateT s m)

instance MonadGriff m => MonadGriff (WriterT w m)

instance MonadGriff m => MonadGriff (UniqT m)

data Opt = Opt
  { srcName :: String,
    dstName :: String,
    dumpParsed :: Bool,
    dumpRenamed :: Bool,
    dumpTyped :: Bool,
    dumpDesugar :: Bool,
    noOptimize :: Bool,
    noLambdaLift :: Bool,
    inlineSize :: Int,
    viaBinding :: Bool,
    debugMode :: Bool
  }
  deriving stock (Eq, Show)

parseOpt :: IO Opt
parseOpt = do
  opt <-
    execParser $
      info
        ( ( Opt
              <$> strArgument (metavar "SOURCE" <> help "Source file" <> action "file")
              <*> strOption
                ( long "output" <> short 'o' <> metavar "OUTPUT" <> value ""
                    <> help
                      "Write LLVM IR to OUTPUT"
                )
              <*> switch (long "dump-parsed")
              <*> switch (long "dump-renamed")
              <*> switch (long "dump-typed")
              <*> switch (long "dump-desugar")
              <*> switch (long "no-lambdalift")
              <*> switch (long "no-opt")
              <*> fmap read (strOption (long "inline" <> value "10"))
              <*> switch (long "via-binding")
              <*> switch (long "debug-mode")
          )
            <**> helper
        )
        (fullDesc <> progDesc "griff" <> header "griff - a programming language")
  if null (dstName opt)
    then pure opt {dstName = srcName opt & extension .~ ".ll"}
    else pure opt
