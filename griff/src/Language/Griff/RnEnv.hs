{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Griff.RnEnv where

import qualified Data.Map as Map
import Koriel.Id
import Koriel.MonadUniq
import Koriel.Prelude
import Language.Griff.Extension

newtype RnState = RnState {_infixInfo :: Map RnId (Assoc, Int)}
  deriving stock (Show)
  deriving newtype (Semigroup, Monoid)

infixInfo :: Lens' RnState (Map RnId (Assoc, Int))
infixInfo = lens _infixInfo (\s x -> s { _infixInfo = x})

data RnEnv = RnEnv
  { _varEnv :: Map PsId RnId,
    _typeEnv :: Map PsTId RnTId
  }
  deriving stock (Show)

instance Semigroup RnEnv where
  RnEnv v1 t1 <> RnEnv v2 t2 = RnEnv (v1 <> v2) (t1 <> t2)

instance Monoid RnEnv where
  mempty = RnEnv mempty mempty

varEnv :: Lens' RnEnv (Map PsId RnId)
varEnv = lens _varEnv (\e x -> e { _varEnv = x})

typeEnv :: Lens' RnEnv (Map PsTId RnTId)
typeEnv = lens _typeEnv (\e x -> e { _typeEnv = x})

genRnState :: Monad m => m RnState
genRnState = pure $ RnState mempty

genRnEnv :: MonadUniq m => m RnEnv
genRnEnv = do
  -- generate RnId of primitive functions and operetors
  add_i32 <- newId "add_i32#" ()
  add_i64 <- newId "add_i64#" ()
  -- generate RnTId of primitive types
  int32_t <- newId "Int32#" ()
  int64_t <- newId "Int64#" ()
  float_t <- newId "Float#" ()
  double_t <- newId "Double#" ()
  char_t <- newId "Char#" ()
  string_t <- newId "String#" ()
  pure $
    RnEnv
      { _varEnv = Map.fromList [("add_i32#", add_i32), ("add_i64#", add_i64)],
        _typeEnv =
          Map.fromList
            [ ("Int32#", int32_t),
              ("Int64#", int64_t),
              ("Float#", float_t),
              ("Double#", double_t),
              ("Char#", char_t),
              ("String#", string_t)
            ]
      }
