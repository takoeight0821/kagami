{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE ExplicitForAll        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE StrictData            #-}
module Language.Malgo.Monad
  ( UniqSupply(..)
  , MalgoM(..)
  , MalgoEnv(..)
  , runMalgo
  , MonadMalgo(..)
  , newUniq
  , Opt(..)
  , matchWith
  , malgoError
  ) where

import           Language.Malgo.Pretty
import           Universum

newtype UniqSupply = UniqSupply { unUniqSupply :: IORef Int }

data Opt = Opt
  { _srcName       :: Text
  , _dumpParsed    :: Bool
  , _dumpRenamed   :: Bool
  , _dumpTyped     :: Bool
  , _dumpKNormal   :: Bool
  , _dumpTypeTable :: Bool
  , _dumpClosure   :: Bool
  , _isDebugMode   :: Bool
  } deriving (Eq, Show)

data MalgoEnv = MalgoEnv
  { maUniqSupply :: UniqSupply
  , maOption     :: Opt
  }

runMalgo :: MonadIO m => MalgoM a -> UniqSupply -> Opt -> m a
runMalgo m u opt = liftIO $ runReaderT (unMalgoM m) (MalgoEnv u opt)

class Monad m => MonadMalgo m where
  liftMalgo :: MalgoM a -> m a

newtype MalgoM a = MalgoM { unMalgoM :: ReaderT MalgoEnv IO a }
  deriving (Functor, Applicative, Alternative, Monad, MonadReader MalgoEnv, MonadIO)

instance MonadMalgo MalgoM where
  liftMalgo = id
instance MonadMalgo m => MonadMalgo (ReaderT r m) where
  liftMalgo = lift . liftMalgo
instance MonadMalgo m => MonadMalgo (ExceptT e m) where
  liftMalgo = lift . liftMalgo
instance MonadMalgo m => MonadMalgo (StateT s m) where
  liftMalgo = lift . liftMalgo

newUniq :: MonadMalgo m => m Int
newUniq = liftMalgo $ do
  UniqSupply u <- maUniqSupply <$> ask
  i <- readIORef u
  modifyIORef u (+1)
  return i

malgoError :: (MonadMalgo m) => Doc -> m a
malgoError mes = liftMalgo $ do
  print mes
  exitFailure

matchWith :: forall (c :: * -> Constraint) a b t.
  (c a, c b, Eq t) =>
  (forall v. c v => v -> t) -> a -> b -> Bool
matchWith f a b = f a == f b
