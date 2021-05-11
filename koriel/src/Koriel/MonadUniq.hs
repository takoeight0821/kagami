{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Koriel.MonadUniq where

import Control.Monad.Cont
import Control.Monad.Fix (MonadFix)
import Control.Monad.Identity (IdentityT)
import qualified Control.Monad.Trans.State.Lazy as Lazy
import Koriel.Prelude
import LLVM.IRBuilder.Module (ModuleBuilderT)
import LLVM.IRBuilder.Monad (IRBuilderT)

class Monad m => MonadUniq m where
  getUniqSupply :: m UniqSupply
  default getUniqSupply :: (MonadTrans t, MonadUniq m1, m ~ t m1) => m UniqSupply
  getUniqSupply = lift getUniqSupply
  getUniq :: m Int
  default getUniq :: (MonadTrans t, MonadUniq m1, m ~ t m1) => m Int
  getUniq = lift getUniq

newtype UniqSupply = UniqSupply {uniqSupply :: Int}

newtype UniqT m a = UniqT {unUniqT :: StateT UniqSupply m a}
  deriving newtype (Functor, Applicative, Monad, Alternative, MonadTrans, MonadFix, MonadFail, MonadIO)

runUniqT :: UniqT m a -> UniqSupply -> m (a, UniqSupply)
runUniqT (UniqT m) = runStateT m

instance Monad m => MonadUniq (UniqT m) where
  getUniqSupply = UniqT get
  getUniq = do
    i <- uniqSupply <$> getUniqSupply
    UniqT $ modify (\s -> s {uniqSupply = i + 1})
    pure i

instance MonadUniq m => MonadUniq (IdentityT m)

instance MonadUniq m => MonadUniq (ReaderT r m)

instance MonadUniq m => MonadUniq (ExceptT e m)

instance MonadUniq m => MonadUniq (StateT s m)

instance MonadUniq m => MonadUniq (Lazy.StateT s m)

instance MonadUniq m => MonadUniq (WriterT w m)

instance MonadUniq m => MonadUniq (ContT r m)

instance MonadUniq m => MonadUniq (ModuleBuilderT m)

instance MonadUniq m => MonadUniq (IRBuilderT m)