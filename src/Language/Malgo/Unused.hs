{-# LANGUAGE OverloadedStrings #-}
module Language.Malgo.Unused where

import           Language.Malgo.MIR
import           Language.Malgo.Type
import           Language.Malgo.TypeCheck (TypedID)

used :: Expr TypedID -> [TypedID]
used (Var x)                     = [x]
used (Tuple xs)                  = xs
used (TupleAccess x _)           = [x]
used (CallDir _ xs)              = xs
used (CallCls x xs)              = x:xs
used (Let (ValDec a e) body)     =
  if a `notElem` used body && (typeOf a /= "Unit")
  then used body
  else used e ++ used body
used (Let (ClsDec a _ cls) body) =
  if a `notElem` used body
  then used body
  else cls ++ used body
used (If c t f)                  = c : used t ++ used f
used (BinOp _ x y)               = [x, y]
used _                           = []

remove' :: Expr TypedID -> Expr TypedID
remove' (Let dec@(ValDec a _) body) =
  if a `notElem` used body && (typeOf a /= "Unit")
  then remove' body
  else Let dec (remove' body)
remove' (Let dec@(ClsDec a _ _) body) =
  if a `notElem` used body
  then remove' body
  else Let dec (remove' body)
remove' (If c t f) = If c (remove' t) (remove' f)
remove' x = x

remove :: Program TypedID -> Program TypedID
remove (Program fundec exdec body) =
  Program (map (\(FunDec n a f b) ->
                  FunDec n a f (remove' b)) fundec)
  exdec
  (remove' body)