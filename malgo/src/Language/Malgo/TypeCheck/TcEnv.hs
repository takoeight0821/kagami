{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Malgo.TypeCheck.TcEnv where

import Koriel.MonadUniq
import Koriel.Pretty
import Language.Malgo.Prelude
import Language.Malgo.Rename.RnEnv (RnEnv)
import Language.Malgo.Syntax.Extension
import Language.Malgo.TypeRep.IORef
import qualified Data.HashMap.Strict as HashMap

data TcEnv = TcEnv
  { _varEnv :: HashMap RnId Scheme,
    _typeEnv :: HashMap RnTId TypeDef,
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
            [ "_varEnv" <+> "=" <+> pPrint (HashMap.toList _varEnv),
              "_typeEnv" <+> "=" <+> pPrint (HashMap.toList _typeEnv),
              "_rnEnv" <+> "=" <+> pPrint _rnEnv
            ]
        )

makeLenses ''TcEnv

simpleTypeDef :: Type -> TypeDef
simpleTypeDef x = TypeDef x [] []

overTypeDef :: Monad f => (Type -> f Type) -> TypeDef -> f TypeDef
overTypeDef f = traverseOf constructor f <=< traverseOf (union . traversed . _2) f

genTcEnv :: MonadUniq m => RnEnv -> m TcEnv
genTcEnv rnEnv =
  pure $
    TcEnv
      { _varEnv = mempty,
        _typeEnv = mempty,
        _rnEnv = rnEnv
      }
