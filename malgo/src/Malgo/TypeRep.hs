{-# LANGUAGE TemplateHaskell #-}

module Malgo.TypeRep where

import Data.Binary (Binary)
import Koriel.Id
import Koriel.Pretty
import Malgo.Prelude
import qualified RIO.List as List
import qualified RIO.Map as Map

--------------------------------
-- Common tag representations --
--------------------------------

-- | Runtime representation
data Rep
  = -- | Boxed value
    BoxedRep
  | -- | Int32#
    Int32Rep
  | -- | Int64#
    Int64Rep
  | -- | Float#
    FloatRep
  | -- | Double#
    DoubleRep
  | -- | Char#
    CharRep
  | -- | String#
    StringRep
  deriving stock (Eq, Ord, Show, Generic)

makePrisms ''Rep

instance Binary Rep

instance Pretty Rep where pPrint rep = text $ show rep

-- | Primitive Types
data PrimT = Int32T | Int64T | FloatT | DoubleT | CharT | StringT
  deriving stock (Eq, Show, Ord, Generic)

makePrisms ''PrimT

instance Binary PrimT

instance Pretty PrimT where
  pPrint Int32T = "Int32#"
  pPrint Int64T = "Int64#"
  pPrint FloatT = "Float#"
  pPrint DoubleT = "Double#"
  pPrint CharT = "Char#"
  pPrint StringT = "String#"

--------------------------
-- Type representations --
--------------------------

type Kind = Type

-- | Definition of `Type`
data Type
  = -- | meta variable
    TyMeta (Id Kind)
  | -- type level operator

    -- | application of type constructor
    TyApp Type Type
  | -- | type variable
    TyVar (Id Kind)
  | -- | type constructor
    TyCon (Id Kind)
  | -- primitive type constructor

    -- | primitive types
    TyPrim PrimT
  | -- | function type
    TyArr Type Type
  | -- | tuple type
    TyTuple Int
  | -- record type
    TyRecord (Map (Id ()) Type)
  | -- | lazy type
    TyLazy
  | -- | pointer type
    TyPtr Type
  | -- | bottom type
    TyBottom
  | -- kind constructor

    -- | star
    TYPE Type
  | -- | kind of runtime representation tags
    TyRep
  | -- | runtime representation tag
    Rep Rep
  deriving stock (Eq, Ord, Show, Generic)

instance Binary Type

makePrisms ''Type

instance Pretty Type where
  pPrintPrec _ _ (TyMeta v) = "'" <> pPrint v
  pPrintPrec l d (TyApp t1 t2) =
    maybeParens (d > 10) $ hsep [pPrintPrec l 10 t1, pPrintPrec l 11 t2]
  pPrintPrec _ _ (TyVar v) = pprIdName v
  pPrintPrec l _ (TyCon c) = pPrintPrec l 0 c
  pPrintPrec l _ (TyPrim p) = pPrintPrec l 0 p
  pPrintPrec l d (TyArr t1 t2) =
    maybeParens (d > 10) $ pPrintPrec l 11 t1 <+> "->" <+> pPrintPrec l 10 t2
  pPrintPrec _ _ (TyTuple n) = parens $ sep $ replicate (max 0 (n - 1)) ","
  pPrintPrec l _ (TyRecord kvs) = braces $ sep $ punctuate "," $ map (\(k, v) -> pPrintPrec l 0 k <> ":" <+> pPrintPrec l 0 v) $ Map.toList kvs
  pPrintPrec _ _ TyLazy = "{}"
  pPrintPrec l d (TyPtr ty) = maybeParens (d > 10) $ sep ["Ptr#", pPrintPrec l 11 ty]
  pPrintPrec _ _ TyBottom = "#Bottom"
  pPrintPrec l _ (TYPE rep) = pPrintPrec l 0 rep
  pPrintPrec _ _ TyRep = "#Rep"
  pPrintPrec l _ (Rep rep) = pPrintPrec l 0 rep

-- | Types that have 'Type'
class HasType a where
  typeOf :: a -> Type

class HasKind a where
  kindOf :: a -> Kind

instance HasKind PrimT where
  kindOf Int32T = TYPE $ Rep Int32Rep
  kindOf Int64T = TYPE $ Rep Int64Rep
  kindOf FloatT = TYPE $ Rep FloatRep
  kindOf DoubleT = TYPE $ Rep DoubleRep
  kindOf CharT = TYPE $ Rep CharRep
  kindOf StringT = TYPE $ Rep StringRep

instance HasKind Type where
  kindOf (TyMeta v) = v ^. idMeta
  kindOf (TyApp t1 _) = case kindOf t1 of
    TyArr _ k -> k
    _ -> error "invalid kind"
  kindOf (TyVar v) = v ^. idMeta
  kindOf (TyCon c) = c ^. idMeta
  kindOf (TyPrim p) = kindOf p
  kindOf (TyArr _ t2) = kindOf t2
  kindOf (TyTuple n) = buildTupleKind n
    where
      buildTupleKind 0 = TYPE (Rep BoxedRep)
      buildTupleKind n
        | n > 0 = TyArr (TYPE (Rep BoxedRep)) (buildTupleKind $ n - 1)
        | otherwise = error "invalid tuple constructor"
  kindOf (TyRecord _) = TYPE (Rep BoxedRep)
  kindOf TyLazy = TYPE (Rep BoxedRep)
  kindOf (TyPtr t) = TyArr (kindOf t) (TYPE (Rep BoxedRep))
  kindOf TyBottom = TYPE (Rep BoxedRep)
  kindOf (TYPE rep) = TYPE rep -- Type :: Type
  kindOf TyRep = TyRep -- Rep :: Rep
  kindOf (Rep _) = TyRep

applySubst :: [(Id Kind, Type)] -> Type -> Type
applySubst _ t@TyMeta {} = t
applySubst subst (TyApp t1 t2) = TyApp (applySubst subst t1) (applySubst subst t2)
applySubst subst t@(TyVar v) = fromMaybe t $ List.lookup v subst
applySubst _ t@TyCon {} = t
applySubst _ t@TyPrim {} = t
applySubst subst (TyArr t1 t2) = TyArr (applySubst subst t1) (applySubst subst t2)
applySubst _ t@TyTuple {} = t
applySubst subst (TyRecord kts) = TyRecord $ fmap (applySubst subst) kts
applySubst _ t@TyLazy {} = t
applySubst subst (TyPtr k) = TyPtr $ applySubst subst k
applySubst _ t@TyBottom = t
applySubst subst (TYPE rep) = TYPE $ applySubst subst rep
applySubst _ t@TyRep = t
applySubst _ t@Rep {} = t

buildTyApp :: Foldable t => Type -> t Type -> Type
buildTyApp = List.foldl TyApp

buildTyArr :: Foldable t => t Type -> Type -> Type
buildTyArr ps ret = foldr TyArr ret ps

splitTyConApp :: Type -> Maybe (Id Kind, [Type])
splitTyConApp (TyCon con) = Just (con, [])
splitTyConApp (TyApp t1 t2) = over (mapped . _2) (<> [t2]) $ splitTyConApp t1
splitTyConApp _ = Nothing

expandTypeSynonym :: (At s, Index s ~ Id Kind, IxValue s ~ ([Id Kind], Type)) => s -> Type -> Maybe Type
expandTypeSynonym abbrEnv (splitTyConApp -> Just (con, ts)) =
  case abbrEnv ^. at con of
    Nothing -> Nothing
    Just (ps, orig) -> Just (applySubst (zip ps ts) orig)
expandTypeSynonym _ _ = Nothing

expandAllTypeSynonym :: (At s, Index s ~ Id Kind, IxValue s ~ ([Id Kind], Type)) => s -> Type -> Type
expandAllTypeSynonym _ t@TyMeta {} = t
expandAllTypeSynonym abbrEnv (splitTyConApp -> Just (con, ts)) =
  case abbrEnv ^. at con of
    Nothing -> buildTyApp (TyCon con) $ map (expandAllTypeSynonym abbrEnv) ts
    Just (ps, orig) ->
      -- ネストした型シノニムを展開するため、展開直後の型をもう一度展開する
      expandAllTypeSynonym abbrEnv $ applySubst (zip ps ts) $ expandAllTypeSynonym abbrEnv orig
expandAllTypeSynonym abbrEnv (TyApp t1 t2) = TyApp (expandAllTypeSynonym abbrEnv t1) (expandAllTypeSynonym abbrEnv t2)
expandAllTypeSynonym _ t@TyVar {} = t
expandAllTypeSynonym _ t@TyCon {} = t
expandAllTypeSynonym _ t@TyPrim {} = t
expandAllTypeSynonym abbrEnv (TyArr t1 t2) = TyArr (expandAllTypeSynonym abbrEnv t1) (expandAllTypeSynonym abbrEnv t2)
expandAllTypeSynonym _ t@TyTuple {} = t
expandAllTypeSynonym abbrEnv (TyRecord kts) = TyRecord $ fmap (expandAllTypeSynonym abbrEnv) kts
expandAllTypeSynonym _ t@TyLazy {} = t
expandAllTypeSynonym abbrEnv (TyPtr t) = TyPtr $ expandAllTypeSynonym abbrEnv t
expandAllTypeSynonym _ t@TyBottom {} = t
expandAllTypeSynonym abbrEnv (TYPE rep) = TYPE $ expandAllTypeSynonym abbrEnv rep
expandAllTypeSynonym _ t@TyRep {} = t
expandAllTypeSynonym _ t@Rep {} = t
