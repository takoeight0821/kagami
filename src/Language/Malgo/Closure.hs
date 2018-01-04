module Language.Malgo.Closure (conv) where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.List
import qualified Data.Map.Strict          as Map
import           Data.String
import           Language.Malgo.FreeVars
import qualified Language.Malgo.HIR       as H
import           Language.Malgo.MIR
import           Language.Malgo.Rename    (ID (..))
import           Language.Malgo.Type
import           Language.Malgo.TypeCheck (TypedID (..))
import           Language.Malgo.Utils
import           Text.PrettyPrint

data ClsEnv = ClsEnv { _closures    :: Map.Map TypedID TypedID
                     , _knowns      :: [TypedID]
                     , _revToplevel :: [Decl TypedID]
                     , _revMain     :: [Instr TypedID]
                     , _count       :: Int
                     }
  deriving Show

initClsEnv :: ClsEnv
initClsEnv = ClsEnv Map.empty [] [] [] 0

type Closure a = Malgo ClsEnv a

runClosure :: Closure a -> (Either MalgoError a, ClsEnv)
runClosure m = runMalgo m initClsEnv

conv :: H.Program TypedID -> (Either MalgoError (Program TypedID), ClsEnv)
conv x = runClosure (convProgram x)

throw :: Doc -> Closure a
throw = throwError . ClosureTransError

addKnown :: TypedID -> Closure ()
addKnown name =
  modify $ \e -> e { _knowns = name : _knowns e }

addToplevel :: Decl TypedID -> Closure ()
addToplevel tp =
  modify $ \e -> e { _revToplevel = tp : _revToplevel e }

addClosure :: TypedID -> TypedID -> Closure ()
addClosure orig cls =
  modify $ \e -> e { _closures = Map.insert orig cls (_closures e) }

addMain :: Instr TypedID -> Closure ()
addMain instr =
  modify $ \e -> e { _revMain = instr : _revMain e }

newClsID :: TypedID -> [TypedID] -> Closure TypedID
newClsID (TypedID fn (FunTy params ret)) fv = do
  let ty = ClsTy params ret (map _type fv)
  c <- gets _count
  modify $ \e -> e { _count = c + 1 }
  return (TypedID
           (Internal (_name fn `mappend` fromString "$cls") c)
           ty)

convProgram :: H.Program TypedID
     -> Closure (Program TypedID)
convProgram (H.Program exs body) = do
  mapM_ (addKnown . H._name) exs
  convExterns exs
  -- convLet body
  t <- gets _revToplevel
  m <- gets _revMain
  return $ Program (reverse t) (reverse m)

convExterns :: [H.Extern TypedID] -> Closure ()
convExterns = mapM_ convExtern

convExtern :: H.Extern TypedID -> Closure ()
convExtern (H.ExDec name actual) = do
  addKnown name
  addToplevel $ ExDec name actual

-- convLet :: H.Expr TypedID -> Closure ()
-- convLet (H.Let (H.ValDec var (H.String str)) rest) = do
--   addToplevel (StrDec var str)
--   convLet rest
-- convLet (H.Let (H.ValDec (TypedID var _) val) rest) = do
--   val' <- convExpr val
--   addMain (TypedID var (typeOf val') := val')
--   convLet rest
-- convLet (H.Let (H.FunDec fn params body) rest) = do
--   -- クロージャ変換して_revToplevelに追加
--   topLevelBackup <- gets _revToplevel
--   knownsBackup <- gets _knowns

--   -- fnに自由変数が無いと仮定してbodyをクロージャ変換
--   addKnown fn
--   mapM addKnown params
--   body' <- convLet body

--   knowns <- gets _knowns
--   let bodyFv = freevars body' \\ knowns
--   body' <- if empty bodyFv
--            then return body'
--            else do modify $ \e -> e { _revToplevel = _revToplevel e
--                                     , _knowns = knowns
--                                     }
--                    convLet body'
-- convLet x =
--   addMain (Do undefined)

convExpr (H.Call fn args) = do
  closures <- gets _closures
  case Map.lookup fn closures of
    (Just fn') -> return $ CallCls fn' args
    Nothing    -> return $ CallDir fn args
convExpr (H.If c t f) = If c <$> convExpr t <*> convExpr f
convExpr e@H.Let{} = throw . text $ "unreachable: " ++ show e
convExpr (H.Var x) = do
  closures <- gets _closures
  case Map.lookup x closures of
    (Just x') -> return $ Var x'
    Nothing   -> return $ Var x
convExpr (H.Int x) = return $ Int x
convExpr (H.Float x) = return $ Float x
convExpr (H.Bool x) = return $ Bool x
convExpr (H.Char x) = return $ Char x
convExpr e@H.String{} = throw . text $ "unreachable: " ++ show e
convExpr H.Unit = return Unit
convExpr (H.BinOp op x y) = return $ BinOp op x y
