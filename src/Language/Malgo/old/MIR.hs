{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeSynonymInstances       #-}
module Language.Malgo.MIR where

import           Control.Monad.State
import           Data.String
import           Language.Malgo.KNormal (Type (..))
import qualified Language.Malgo.KNormal as K
import           Language.Malgo.Utils
import           Text.PrettyPrint

data Block = Block { blockName :: Name
                   , blockBody :: [Instr]
                   }
  deriving (Show, Eq)

instance PrettyPrint Block where
  pretty (Block name body) =
    text "BEGIN:" <+> pretty name
    $+$ nest 2 (vcat (map pretty body))
    $+$ text "END: " <+> pretty name

type Instr = ((Name, Type), Val)

instance PrettyPrint Instr where
  pretty ((name, typ), val) =
    pretty typ <+> pretty name <+> text "=" <+> pretty val

data Val = Int Integer
         -- Var Id Type
         | Float Double
         | Bool Bool
         | Char Char
         | String String
         | Unit
         | App (Name, Type) [(Name, Type)]
         | AppCls (Name, Type) [(Name, Type)]
         | MkCls (Name, Type) [(Name, Type)]
         -- | Fun free_vars parameter return_type body
         | Fun [(Name, Type)] [(Name, Type)] Type Block
         | If (Name, Type) Block Block
         | BinOp Op (Name, Type) (Name, Type)
  deriving (Show, Eq)

instance PrettyPrint Val where
  -- pretty (Var name _)      = pretty name
  pretty (Int x)         = text "int" <+> integer x
  pretty (Float x)       = text "float" <+> double x
  pretty (Bool True)     = text "bool" <+> text "#t"
  pretty (Bool False)    = text "bool" <+> text "#f"
  pretty (Char x)        = text "char" <+> quotes (char x)
  pretty (String x)      = text "string" <+> doubleQuotes (text x)
  pretty Unit            = text "unit"
  pretty (App fn arg)    = text "app" <+> sep (pretty fn : map pretty arg)
  pretty (AppCls fn arg) = text "appcls" <+> sep (pretty fn : map pretty arg)
  pretty (MkCls fn capture) = text "mkcls" <+> sep (pretty fn : map pretty capture)
  pretty (Fun fv params retTy body) =
    text "fun" <+> braces (sep (map pretty fv)) <+> sep (map pretty params) <+> pretty retTy
    $+$ pretty body
  pretty (If c t f) =
    text "if" <+> pretty c
    $+$ nest 2 (pretty t)
    $+$ nest 2 (pretty f)
  pretty (BinOp op x y) = text "binop" <+> pretty op <+> pretty x <+> pretty y

data MIRState = MIRState { count :: Int
                         , table :: [(Name, Name)]
                         }
  deriving Show

newtype MIR a = MIR (StateT MIRState (Either String) a)
  deriving (Functor, Applicative, Monad, MonadState MIRState)

runMIR :: MIR a -> Either String (a, MIRState)
runMIR (MIR m) = runStateT m (MIRState 0 [])

newId :: Name -> MIR Name
newId hint = do
  c <- gets count
  modify $ \e -> e { count = count e + 1
                   , table = ( hint
                             , hint `mappend` "." `mappend` fromString (show c)
                             ) : table e
                   }
  return $ hint `mappend` "." `mappend` fromString (show c)

incCount :: Int -> MIR ()
incCount n = modify $ \e -> e { count = count e + n }

getId :: Name -> MIR Name
getId name = do
  t <- gets table
  case lookup name t of
    Just x  -> return x
    Nothing -> newId name

-- toMIR :: K.Expr -> Either String (Block, Int)
-- toMIR :: K.Expr -> Either String ([Instr], Int)

toMIR :: K.Expr -> Int -> Either String (Block, Int)
toMIR expr source = do
  m <- runMIR $ do
    incCount source
    root <- newId "root"
    toBlock root expr
  return (fst m, count (snd m))

toBlock :: Name -> K.Expr -> MIR Block
toBlock label body = Block label <$> toBlock' body

toBlock' :: K.Expr -> MIR [Instr]
toBlock' (K.Let (K.ValDec name typ val) body, _) = do
  val' <- toVal val
  rest <- toBlock' body
  return $ ((name, typ), val') : rest

toBlock' (K.Let (K.FunDec fn params retTy fnBody) body, _) = do
  fnBody' <- func
  rest <- toBlock' body
  return $ ((fn, fnTy), fnBody') : rest
  where func = do
          fnLabel <- newId fn
          Fun [] params retTy <$> toBlock fnLabel fnBody
        fnTy = FunTy (TupleTy (map snd params)) retTy

toBlock' e@(_, t) = do
  n <- newId "$m"
  e' <- toVal e
  return [((n, t), e')]

toVal :: K.Expr -> MIR Val
toVal (K.If c t f, _) = do
  tlabel <- newId "then"
  flabel <- newId "else"
  t' <- toBlock tlabel t
  f' <- toBlock flabel f
  return $ If c t' f'
-- toVal (K.Var name, ty)       = return $ Var name ty
toVal (K.Int x, _)          = return $ Int x
toVal (K.Float x, _)        = return $ Float x
toVal (K.Bool x, _)         = return $ Bool x
toVal (K.Char x, _)         = return $ Char x
toVal (K.String x, _)       = return $ String x
toVal (K.Unit, _)           = return Unit
toVal (K.Call fn params, _) = return $ App fn params
toVal (K.BinOp op x y, _) = return $ BinOp op x y
toVal e@(_, _) =
  MIR $ lift . Left $ "unreachable clause: toVal " ++ show e