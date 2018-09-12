{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE ExplicitForAll             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE StrictData                 #-}
module Language.Malgo.Old.Monad
  ( UniqSupply(..)
  , MalgoM(..)
  , MalgoEnv(..)
  , runMalgo
  , MonadMalgo(..)
  , newUniq
  , Opt(..)
  , malgoError
  ) where

import           Universum

newtype UniqSupply = UniqSupply (IORef Int)

data Opt = Opt
  { srcName       :: String
  , dstName       :: String
  , dumpParsed    :: Bool
  , dumpRenamed   :: Bool
  , dumpTyped     :: Bool
  , dumpKNormal   :: Bool
  , dumpTypeTable :: Bool
  , dumpClosure   :: Bool
  , isDebugMode   :: Bool
  } deriving (Eq, Show)

data MalgoEnv = MalgoEnv
  { maUniqSupply :: UniqSupply
  , maOption     :: Opt
  }

newtype MalgoM a = MalgoM { unMalgoM :: ReaderT MalgoEnv IO a }
  deriving (Functor, Applicative, Alternative, Monad, MonadReader MalgoEnv, MonadIO)

runMalgo :: MonadIO m => MalgoM a -> UniqSupply -> Opt -> m a
runMalgo (MalgoM m) u opt = liftIO $ runReaderT m (MalgoEnv u opt)

class MonadIO m => MonadMalgo m where
  liftMalgo :: MalgoM a -> m a

instance MonadMalgo MalgoM where
  liftMalgo = identity
instance MonadMalgo m => MonadMalgo (ReaderT r m) where
  liftMalgo = lift . liftMalgo
instance MonadMalgo m => MonadMalgo (ExceptT e m) where
  liftMalgo = lift . liftMalgo
instance MonadMalgo m => MonadMalgo (StateT s m) where
  liftMalgo = lift . liftMalgo

newUniq :: MonadMalgo m => m Int
newUniq = liftMalgo $ do
  UniqSupply u <- asks maUniqSupply
  i <- readIORef u
  modifyIORef u (+1)
  return i

malgoError :: (MonadIO m, Show a) => a -> m b
malgoError mes = do
  print mes
  exitFailure