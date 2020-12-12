{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Koriel.Id
  ( Id,
    idName,
    idUniq,
    idMeta,
    idIsGlobal,
    newId,
    newGlobalId,
  )
where

import Data.Store (Store)
import Koriel.MonadUniq
import Koriel.Prelude hiding (toList)
import Koriel.Pretty

data Id a = Id
  { _idName :: String,
    _idUniq :: Int,
    _idMeta :: a,
    _idIsGlobal :: Bool
  }
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Generic)

instance Store a => Store (Id a)

#ifndef DEBUG
instance Pretty a => Pretty (Id a) where
  pPrint (Id n _ _ True) = text n
  pPrint (Id n u _ False) = text n <> "." <> text (show u)
#else
instance Pretty a => Pretty (Id a) where
  pPrint (Id n _ m True) = text n <> braces (pPrint m)
  pPrint (Id n u m False) = text n <> "." <> text (show u) <> braces (pPrint m)
#endif

idName :: Getter (Id a) String
idName = to _idName

idUniq :: Getter (Id a) Int
idUniq = to _idUniq

idMeta :: Lens (Id a) (Id b) a b
idMeta = lens _idMeta (\i x -> i {_idMeta = x})

idIsGlobal :: Lens' (Id a) Bool
idIsGlobal = lens _idIsGlobal (\i x -> i {_idIsGlobal = x})

newId :: MonadUniq f => String -> a -> f (Id a)
newId n m = Id n <$> getUniq <*> pure m <*> pure False

newGlobalId :: MonadUniq f => String -> a -> f (Id a)
newGlobalId n m = Id n <$> getUniq <*> pure m <*> pure True
