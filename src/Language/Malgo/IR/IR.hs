{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}
module Language.Malgo.IR.IR where

import           Control.Lens                      (view, _1, _3)
import           Language.Malgo.MiddleEnd.FreeVars
import           Language.Malgo.Pretty
import           Language.Malgo.TypeRep.MType
import           Relude

data Program a = Program a [Defn a]
  deriving (Show, Eq, Read, Generic, PrettyVal)

flattenProgram :: Program a -> Program a
flattenProgram (Program m defs) = Program m (map flattenDefn defs)

instance FreeVars Program where
  freevars (Program _ xs) = mconcat $ map freevars xs

instance Pretty a => Pretty (Program a) where
  pPrint (Program _ defns) =
    sep (map pPrint defns)

data Defn a = DefFun { _fnName   :: a
                     , _fnParams :: [a]
                     , _fnBody   :: Expr a
                     }
  deriving (Show, Eq, Read, Generic, PrettyVal)

flattenDefn :: Defn a -> Defn a
flattenDefn (DefFun f params body) = DefFun f params (flattenExpr body)

instance FreeVars Defn where
  freevars (DefFun _ params body) =
    freevars body \\ fromList params

instance Pretty a => Pretty (Defn a) where
  pPrint (DefFun fn params body) =
    parens ("define" <+> parens (pPrint fn <+> parens (sep (map pPrint params))) $+$ nest 2 (pPrint body))

{- Closure representation

Tuple [fn :: FunctionTy ret [PointerTy (IntTy 8), x, y, ...], Cast (PointerTy (IntTy 8)) (Tuple ..)]

cls = Tuple [fn, env]
fn = Access cls [0, 0]
env = Access cls [0, 1]
Apply fn (env : args)
-}

data Expr a = Var a
            | Int Integer
            | Float Double
            | Bool Bool
            | Char Char
            | String Text
            | Unit
            | Prim Text MType
            | Tuple [a]
            | MakeArray MType a
            | Read a a
            | Write a a a
            | Apply a [a]
            | Let a (Expr a) (Expr a)
            | LetRec [(a, [a], Expr a)] (Expr a)
            | Cast MType a
            | Access a [Int]
            | Store a [Int] a
            | If a (Expr a) (Expr a)
  deriving (Show, Eq, Read, Functor, Foldable, Traversable, Generic, PrettyVal)

flattenExpr :: Expr a -> Expr a
flattenExpr (Let x v1 e1) =
  insert (flattenExpr v1)
  where insert (Let y v2 e2) = Let y v2 (insert e2)
        insert (LetRec xs e) = LetRec xs (insert e)
        insert v             = Let x v (flattenExpr e1)
flattenExpr (LetRec defs body) =
  LetRec (map flattenDef defs) (flattenExpr body)
  where flattenDef (f, p, e) = (f, p, flattenExpr e)
flattenExpr (If c t f) = If c (flattenExpr t) (flattenExpr f)
flattenExpr e = e

prims :: Expr a -> [Expr a]
prims p@Prim{} = [p]
prims (Let _ v e) = prims v ++ prims e
prims (LetRec vs e) = prims' ++ prims e
  where prims' = concatMap (prims . view _3) vs
prims (If _ t f) = prims t ++ prims f
prims _ = []

instance FreeVars Expr where
  freevars (Var x) = one x
  freevars (Tuple xs) = fromList xs
  freevars (Apply _ args) = fromList args
  freevars (Let x v e) = freevars v <> delete x (freevars e)
  freevars (LetRec xs e) =
    (mconcat (map (\(_, params, body) -> freevars body \\ fromList params) xs) <> freevars e)
    \\ fromList (map (view _1) xs)
  freevars (Cast _ x) = one x
  freevars (Access x _) = one x
  freevars (Store x _ y) = fromList [x, y]
  freevars (If c t f) = one c <> freevars t <> freevars f
  freevars _ = mempty

instance Pretty a => Pretty (Expr a) where
  pPrint (Var a) = pPrint a
  pPrint (Int i) = pPrint i
  pPrint (Float d) = pPrint d
  pPrint (Bool True) = "true"
  pPrint (Bool False) = "false"
  pPrint (Char c) = quotes $ pPrint c
  pPrint (String s) = doubleQuotes $ pPrint s
  pPrint Unit = lparen <> rparen
  pPrint (MakeArray ty size) = "array" <> parens (pPrint ty <> "," <+> pPrint size)
  pPrint (Read arr ix) = pPrint arr <> brackets (pPrint ix)
  pPrint (Write arr ix val) = parens $ pPrint arr <> brackets (pPrint ix) <+> "<-" <+> pPrint val
  pPrint (Prim name _) = "#" <> pPrint name
  pPrint (Tuple xs) = "tuple" <> parens (sep $ punctuate "," $ map pPrint xs)
  pPrint (Apply f args) = parens (pPrint f <+> sep (map pPrint args))
  pPrint (Let name val body) =
    parens ("let" <+> parens (pPrint name <+> pPrint val)
            $+$ nest 1 (pPrint body))
  pPrint (LetRec defs body) =
    parens ("let" <+> sep (map (\(name, params, val) ->
                                   parens ("rec" <+> pPrint name <+> sep (map pPrint params)
                                            $+$ nest 1 (pPrint val))) defs)
            $+$ nest 1 (pPrint body))
  pPrint (Cast ty val) = parens ("cast" <+> pPrint ty <+> pPrint val)
  pPrint (Access e is) = parens ("access" <+> pPrint e <+> sep (map pPrint is))
  pPrint (Store var is val) = parens ("store" <+> pPrint var <+> sep (map pPrint is) <+> pPrint val)
  pPrint (If c t f) =
    parens ("if" <+> (pPrint c $+$ pPrint t $+$ pPrint f))

instance (HasMType a, PrettyVal a) => HasMType (Expr a) where
  mTypeOf (Var a) = mTypeOf a
  mTypeOf (Int _) = IntTy 64
  mTypeOf (Float _) = DoubleTy
  mTypeOf (Bool _) = IntTy 1
  mTypeOf (Char _) = IntTy 8
  mTypeOf (String _) = PointerTy (IntTy 8)
  mTypeOf Unit = StructTy []
  mTypeOf (MakeArray ty _) = PointerTy ty
  mTypeOf (Read arr _) =
    case mTypeOf arr of
      PointerTy t -> t
      t           -> error $ show $ pPrint t <+> "is not array"
  mTypeOf Write{} = StructTy []
  mTypeOf (Prim _ ty) = ty
  mTypeOf (Tuple xs) = PointerTy (StructTy (map mTypeOf xs))
  mTypeOf (Apply f _) =
    case mTypeOf f of
      FunctionTy t _ -> t -- normal function
      -- PointerTy (StructTy [FunctionTy t _, _]) -> t -- closure
      t              -> error $ show $ pPrint t <+> "is not applieable"
  mTypeOf (Let _ _ body) = mTypeOf body
  mTypeOf (LetRec _ body) = mTypeOf body
  mTypeOf (Cast ty _) = ty
  mTypeOf (Access e is) =
    case runIdentity $ runExceptT (accessMType (mTypeOf e) is) of
      Right t  -> t
      Left mes -> error $ show $ dumpDoc (Access e is) <+> mes
  mTypeOf (Store var is val) =
    case runIdentity $ runExceptT (accessMType (mTypeOf var) is) of
      Right t | t == mTypeOf val -> StructTy []
              | otherwise -> error "mTypeOf(Store)"
      Left mes -> error $ show $ dumpDoc (Store var is val) <+> mes
  mTypeOf (If _ e _) = mTypeOf e
