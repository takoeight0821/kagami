module Language.Malgo.Beta (betaTrans) where

import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.Map.Strict          as Map
import           Data.Maybe
import           Language.Malgo.HIR
import           Language.Malgo.TypeCheck (TypedID (..))
import           Language.Malgo.Utils

newtype BEnv = BEnv { _table :: Map.Map TypedID TypedID }

initBEnv :: BEnv
initBEnv = BEnv Map.empty

type Beta a = Malgo BEnv a

runBeta :: Beta a -> (Either MalgoError a, BEnv)
runBeta m = runMalgo m initBEnv

betaTrans :: Expr TypedID -> (Either MalgoError (Expr TypedID), BEnv)
betaTrans prog = runBeta $ transExpr prog

addBind :: TypedID -> TypedID -> Beta ()
addBind x y =
  modify $ \e -> e { _table = Map.insert x y (_table e) }

find :: TypedID -> Beta TypedID
find x = do
  table <- gets _table
  let x' = Map.lookup x table
  return $ fromMaybe x x'

transExpr :: Expr TypedID -> Beta (Expr TypedID)
transExpr (Let (FunDec fn params fnbody) body) =
  Let <$> (FunDec fn params <$> transExpr fnbody) <*> transExpr body
transExpr (Let (ValDec name val) body) = do
  val' <- transExpr val
  case val' of
    (Var x) ->
      addBind name x >> Let (ValDec name val') <$> transExpr body
    _ -> Let (ValDec name val') <$> transExpr body
transExpr (BinOp op x y) =
  BinOp op <$> find x <*> find y
transExpr (If c t f) =
  If <$> find c <*> transExpr t <*> transExpr f
transExpr (Call fn args) =
  Call <$> find fn <*> mapM find args
transExpr (Var x) = Var <$> find x
transExpr x = return x