{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Griff.TcEnv where

import qualified Data.Map as Map
import Koriel.MonadUniq
import Language.Griff.Extension
import Language.Griff.Prelude
import Language.Griff.RnEnv
  ( RnEnv,
  )
import qualified Language.Griff.RnEnv as R
import Language.Griff.Type

data TcEnv = TcEnv
  { _varEnv :: Map RnId Scheme,
    _typeEnv :: Map RnTId Type,
    _tyConEnv :: Map TyCon ([TyVar], [(RnId, Type)]),
    _rnEnv :: RnEnv
  }
  deriving stock (Show, Eq)

instance Semigroup TcEnv where
  TcEnv v1 t1 c1 r1 <> TcEnv v2 t2 c2 r2 = TcEnv (v1 <> v2) (t1 <> t2) (c1 <> c2) (r1 <> r2)

instance Monoid TcEnv where
  mempty = TcEnv mempty mempty mempty mempty

varEnv :: Lens' TcEnv (Map RnId Scheme)
varEnv = lens _varEnv (\e x -> e {_varEnv = x})

typeEnv :: Lens' TcEnv (Map RnTId Type)
typeEnv = lens _typeEnv (\e x -> e {_typeEnv = x})

tyConEnv :: Lens' TcEnv (Map TyCon ([TyVar], [(RnId, Type)]))
tyConEnv = lens _tyConEnv (\e x -> e {_tyConEnv = x})

rnEnv :: Lens' TcEnv RnEnv
rnEnv = lens _rnEnv (\e x -> e {_rnEnv = x})

genTcEnv :: MonadUniq m => RnEnv -> m TcEnv
genTcEnv rnEnv = do
  -- lookup RnId of primitive functions and operetors
  let add_i32 = fromJust $ Map.lookup "add_i32#" (view R.varEnv rnEnv)
  let add_i64 = fromJust $ Map.lookup "add_i64#" (view R.varEnv rnEnv)
  -- lookup RnTId of primitive types
  let int32_t = fromJust $ Map.lookup "Int32#" (view R.typeEnv rnEnv)
  let int64_t = fromJust $ Map.lookup "Int64#" (view R.typeEnv rnEnv)
  let float_t = fromJust $ Map.lookup "Float#" (view R.typeEnv rnEnv)
  let double_t = fromJust $ Map.lookup "Double#" (view R.typeEnv rnEnv)
  let string_t = fromJust $ Map.lookup "String#" (view R.typeEnv rnEnv)
  pure $
    TcEnv
      { _varEnv =
          Map.fromList
            [ ( add_i32,
                Forall [] (TyTuple [TyPrim Int32T, TyPrim Int32T] `TyArr` TyPrim Int32T)
              ),
              ( add_i64,
                Forall [] (TyTuple [TyPrim Int64T, TyPrim Int64T] `TyArr` TyPrim Int64T)
              )
            ],
        _typeEnv =
          Map.fromList
            [ (int32_t, TyPrim Int32T),
              (int64_t, TyPrim Int64T),
              (float_t, TyPrim FloatT),
              (double_t, TyPrim DoubleT),
              (string_t, TyPrim StringT)
            ],
        _tyConEnv = mempty,
        _rnEnv = rnEnv
      }
