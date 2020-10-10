{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Griff.Extension where

import Data.Kind (Constraint)
import qualified Data.Kind as K
import Koriel.Id
import Koriel.Prelude
import Koriel.Pretty
import Language.Griff.Type
import Text.Megaparsec.Pos (SourcePos)

data Assoc = LeftA | RightA | NeutralA
  deriving stock (Eq, Show)

instance Pretty Assoc where
  pPrint LeftA = "l"
  pPrint RightA = "r"
  pPrint NeutralA = ""

type family XId x

-- Exp Extensions
type family XVar x

type family XCon x

type family XUnboxed x

type family XApply x

type family XOpApp x

type family XFn x

type family XTuple x

type family XForce x

type ForallExpX (c :: K.Type -> Constraint) x =
  ( c (XVar x),
    c (XCon x),
    c (XUnboxed x),
    c (XApply x),
    c (XOpApp x),
    c (XFn x),
    c (XTuple x),
    c (XForce x)
  )

-- Clause Extensions
type family XClause x

type ForallClauseX (c :: K.Type -> Constraint) x = c (XClause x)

-- Pat Extensions
type family XVarP x

type family XConP x

type family XUnboxedP x

type ForallPatX (c :: K.Type -> Constraint) x = (c (XVarP x), c (XConP x), c (XUnboxedP x))

-- Type Extensions
type family XTId x

type family XTyApp x

type family XTyVar x

type family XTyCon x

type family XTyArr x

type family XTyTuple x

type family XTyLazy x

type ForallTypeX (c :: K.Type -> Constraint) x =
  (c (XTyApp x), c (XTyVar x), c (XTyCon x), c (XTyArr x), c (XTyTuple x), c (XTyLazy x))

-- Decl Extensions
type family XScDef x

type family XScSig x

type family XDataDef x

type family XInfix x

type family XForign x

type ForallDeclX (c :: K.Type -> Constraint) x =
  ( c (XScDef x),
    c (XScSig x),
    c (XDataDef x),
    c (XInfix x),
    c (XForign x),
    ForallExpX c x,
    ForallClauseX c x,
    ForallPatX c x,
    ForallTypeX c x
  )

-- Phase and type instance
data GriffPhase = Parse | Rename | TypeCheck

data Griff (p :: GriffPhase)

type family GriffId (p :: GriffPhase) where
  GriffId 'Parse = String
  GriffId 'Rename = Id ()
  GriffId 'TypeCheck = Id ()

type family GriffTId (p :: GriffPhase) where
  GriffTId 'Parse = String
  GriffTId 'Rename = Id ()
  GriffTId 'TypeCheck = Id ()

type instance XVar (Griff 'Parse) = SourcePos

type instance XVar (Griff 'Rename) = SourcePos

type instance XVar (Griff 'TypeCheck) = WithType SourcePos

type instance XCon (Griff 'Parse) = SourcePos

type instance XCon (Griff 'Rename) = SourcePos

type instance XCon (Griff 'TypeCheck) = WithType SourcePos

type instance XId (Griff p) = GriffId p

type instance XUnboxed (Griff 'Parse) = SourcePos

type instance XUnboxed (Griff 'Rename) = SourcePos

type instance XUnboxed (Griff 'TypeCheck) = WithType SourcePos

type instance XApply (Griff 'Parse) = SourcePos

type instance XApply (Griff 'Rename) = SourcePos

type instance XApply (Griff 'TypeCheck) = WithType SourcePos

type instance XOpApp (Griff 'Parse) = SourcePos

type instance XOpApp (Griff 'Rename) = (SourcePos, (Assoc, Int))

type instance XOpApp (Griff 'TypeCheck) = WithType (SourcePos, (Assoc, Int))

type instance XFn (Griff 'Parse) = SourcePos

type instance XFn (Griff 'Rename) = SourcePos

type instance XFn (Griff 'TypeCheck) = WithType SourcePos

type instance XTuple (Griff 'Parse) = SourcePos

type instance XTuple (Griff 'Rename) = SourcePos

type instance XTuple (Griff 'TypeCheck) = WithType SourcePos

type instance XForce (Griff 'Parse) = SourcePos

type instance XForce (Griff 'Rename) = SourcePos

type instance XForce (Griff 'TypeCheck) = WithType SourcePos

type instance XClause (Griff 'Parse) = SourcePos

type instance XClause (Griff 'Rename) = SourcePos

type instance XClause (Griff 'TypeCheck) = WithType SourcePos

type instance XVarP (Griff 'Parse) = SourcePos

type instance XVarP (Griff 'Rename) = SourcePos

type instance XVarP (Griff 'TypeCheck) = WithType SourcePos

type instance XConP (Griff 'Parse) = SourcePos

type instance XConP (Griff 'Rename) = SourcePos

type instance XConP (Griff 'TypeCheck) = WithType SourcePos

type instance XUnboxedP (Griff 'Parse) = SourcePos

type instance XUnboxedP (Griff 'Rename) = SourcePos

type instance XUnboxedP (Griff 'TypeCheck) = WithType SourcePos

type instance XTId (Griff p) = GriffTId p

type instance XTyApp (Griff _) = SourcePos

type instance XTyVar (Griff _) = SourcePos

type instance XTyCon (Griff _) = SourcePos

type instance XTyArr (Griff _) = SourcePos

type instance XTyTuple (Griff _) = SourcePos

type instance XTyLazy (Griff _) = SourcePos

type instance XScDef (Griff 'Parse) = SourcePos

type instance XScDef (Griff 'Rename) = SourcePos

type instance XScDef (Griff 'TypeCheck) = WithType SourcePos

type instance XScSig (Griff _) = SourcePos

type instance XDataDef (Griff _) = SourcePos

type instance XInfix (Griff _) = SourcePos

type instance XForign (Griff 'Parse) = SourcePos

type instance XForign (Griff 'Rename) = (SourcePos, String)

type instance XForign (Griff 'TypeCheck) = WithType (SourcePos, String)