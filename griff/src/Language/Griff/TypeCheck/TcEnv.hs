{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Griff.TypeCheck.TcEnv where

import qualified Data.Map as Map
import Data.Store
import Koriel.MonadUniq
import Koriel.Pretty
import Language.Griff.Prelude
import Language.Griff.Rename.RnEnv
  ( RnEnv,
  )
import qualified Language.Griff.Rename.RnEnv as R
import Language.Griff.Syntax.Extension
import Language.Griff.Type

data TcEnv = TcEnv
  { _varEnv :: Map RnId Scheme,
    _typeEnv :: Map RnTId TypeDef,
    _rnEnv :: RnEnv
  }
  deriving stock (Show, Eq)

instance Semigroup TcEnv where
  TcEnv v1 t1 r1 <> TcEnv v2 t2 r2 = TcEnv (v1 <> v2) (t1 <> t2) (r1 <> r2)

instance Monoid TcEnv where
  mempty = TcEnv mempty mempty mempty

instance Pretty TcEnv where
  pPrint TcEnv {_varEnv, _typeEnv, _rnEnv} =
    "TcEnv"
      <+> braces
        ( sep
            [ "_varEnv" <+> "=" <+> pPrint (Map.toList _varEnv),
              "_typeEnv" <+> "=" <+> pPrint (Map.toList _typeEnv),
              "_rnEnv" <+> "=" <+> pPrint _rnEnv
            ]
        )

data TypeDef = TypeDef {_constructor :: Type, _qualVars :: [TyVar], _union :: [(RnId, Type)]}
  deriving stock (Show, Eq, Generic)
  deriving anyclass (Store)

instance Pretty TypeDef where
  pPrint (TypeDef c q u) = pPrint (c, q, u)

makeLenses ''TcEnv

makeLenses ''TypeDef

simpleTypeDef :: Type -> TypeDef
simpleTypeDef x = TypeDef x [] []

overTypeDef :: Monad f => (Type -> f Type) -> TypeDef -> f TypeDef
overTypeDef f = traverseOf constructor f <=< traverseOf (union . traversed . _2) f

genTcEnv :: MonadUniq m => RnEnv -> m TcEnv
genTcEnv rnEnv = do
  -- lookup RnTId of primitive types
  let int32_t = fromJust $ Map.lookup "Int32#" (view R.typeEnv rnEnv)
  let int64_t = fromJust $ Map.lookup "Int64#" (view R.typeEnv rnEnv)
  let float_t = fromJust $ Map.lookup "Float#" (view R.typeEnv rnEnv)
  let double_t = fromJust $ Map.lookup "Double#" (view R.typeEnv rnEnv)
  let char_t = fromJust $ Map.lookup "Char#" (view R.typeEnv rnEnv)
  let string_t = fromJust $ Map.lookup "String#" (view R.typeEnv rnEnv)
  pure $
    TcEnv
      { _varEnv = mempty,
        _typeEnv =
          Map.fromList
            [ (int32_t, TypeDef (TyPrim Int32T) [] []),
              (int64_t, TypeDef (TyPrim Int64T) [] []),
              (float_t, TypeDef (TyPrim FloatT) [] []),
              (double_t, TypeDef (TyPrim DoubleT) [] []),
              (char_t, TypeDef (TyPrim CharT) [] []),
              (string_t, TypeDef (TyPrim StringT) [] [])
            ],
        _rnEnv = rnEnv
      }
