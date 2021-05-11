{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Malgo.Prelude
  ( module Koriel.Prelude,
    MonadMalgo (..),
    MalgoM (..),
    MalgoEnv (..),
    errorOn,
    Opt (..),
    defaultOpt,
    With (..),
    ann,
    value,
  )
where

import Control.Monad.Fix (MonadFix)
import Data.Kind (Type)
import Koriel.MonadUniq
import Koriel.Prelude
import Koriel.Pretty
import System.FilePath ((-<.>))
import Text.Megaparsec.Pos (SourcePos (sourceLine), unPos)

newtype MalgoM a = MalgoM {unMalgoM :: UniqT (ReaderT (MalgoEnv MalgoM) IO) a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadFix, MonadFail, MonadUniq)

class MonadIO m => MonadMalgo m where
  getOpt :: m Opt
  default getOpt :: (MonadTrans t, MonadMalgo m1, m ~ t m1) => m Opt
  getOpt = lift getOpt

viewLine :: MonadMalgo m => Int -> m String
viewLine linum = do
  srcFileName <- srcName <$> getOpt
  s <- liftIO $ readFile srcFileName
  pure $ lines s !! (linum - 1)

#ifdef DEBUG
errorOn :: (HasCallStack, MonadMalgo m) => SourcePos -> Doc -> m a
#else
errorOn :: MonadMalgo m => SourcePos -> Doc -> m a
#endif
errorOn pos x = do
  line <- viewLine (unPos $ sourceLine pos)
  errorDoc $
    "error on" <+> pPrint pos <> ":" $+$ nest 2 x
      $+$ pPrint (unPos $ sourceLine pos) <+> "|" <+> text line

instance MonadMalgo MalgoM where
  getOpt = MalgoM $ lift $ asks _malgoOpt

instance MonadMalgo m => MonadMalgo (ReaderT r m)

instance MonadMalgo m => MonadMalgo (ExceptT e m)

instance MonadMalgo m => MonadMalgo (StateT s m)

instance MonadMalgo m => MonadMalgo (WriterT w m)

instance MonadMalgo m => MonadMalgo (UniqT m)

data Opt = Opt
  { srcName :: FilePath,
    dstName :: FilePath,
    dumpParsed :: Bool,
    dumpRenamed :: Bool,
    dumpTyped :: Bool,
    dumpDesugar :: Bool,
    noOptimize :: Bool,
    noLambdaLift :: Bool,
    inlineSize :: Int,
    debugMode :: Bool,
    modulePaths :: [FilePath],
    forceRebuild :: Bool
  }
  deriving stock (Eq, Show)

defaultOpt :: FilePath -> Opt
defaultOpt src =
  Opt
    { srcName = src,
      dstName = src -<.> "ll",
      dumpParsed = False,
      dumpRenamed = False,
      dumpTyped = False,
      dumpDesugar = False,
      noOptimize = False,
      noLambdaLift = False,
      inlineSize = 10,
      debugMode = False,
      modulePaths = [],
      forceRebuild = False
    }

newtype MalgoEnv (m :: Type -> Type) = MalgoEnv {_malgoOpt :: Opt}

data With x v = With {_ann :: x, _value :: v}
  deriving stock (Eq, Ord, Bounded, Read, Show, Generic)

makeLenses ''With

instance (Pretty x, Pretty v) => Pretty (With x v) where
  pPrintPrec l _ (With x v) = pPrintPrec l 0 v <> brackets (pPrintPrec l 0 x)
