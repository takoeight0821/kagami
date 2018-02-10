{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Malgo.CodeGen where

import           Debug.Trace

import           Control.Monad.State.Strict
import           Data.Char
import qualified Data.Map.Strict                 as Map
import           Data.Maybe
import           Data.String
import qualified Data.Text.Lazy.IO               as Text

import qualified LLVM.AST.Constant               as C
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.Global                 as G
import qualified LLVM.AST.IntegerPredicate       as IP
import           LLVM.AST.Operand
import qualified LLVM.AST.Type                   as LT
import           LLVM.AST.Typed
import           LLVM.IRBuilder                  as IRBuilder
import           LLVM.Pretty

import           Language.Malgo.HIR              (Op (..))
import           Language.Malgo.MIR
import           Language.Malgo.Rename           (ID (..))
import qualified Language.Malgo.Type             as T
import           Language.Malgo.TypeCheck        (TypedID (..))
import           Language.Malgo.Utils

-- test = T.putStrLn $ ppllvm $ buildModule "test" $ mdo
--   f <- function "fun" [(i32, "n")] i32 $ \[n] ->
--     do r <- call f [(n, [])]
--        ret r
--   return f

data GenState = GenState { _table    :: Map.Map TypedID Operand
                         , _term     :: Operand -> GenExpr () -- if式の際の最終分岐先などに利用
                         , _internal :: Map.Map String Operand
                         }

type GenExpr a = IRBuilderT GenDec a
type GenDec = ModuleBuilderT (State GenState)

-- addFunction :: TypedID -> Operand -> GenDec ()
-- addFunction name opr =
--   lift (modify (\s -> s { _table = Map.insert name opr (_table s)}))

-- addTable :: TypedID -> Operand -> GenExpr ()
addTable name opr =
  lift (modify (\s -> s { _table = Map.insert name opr (_table s)}))

-- addInternal :: String -> Operand -> GenExpr ()
addInternal name opr =
  lift (modify (\s -> s { _internal = Map.insert name opr (_internal s) }))

convertType :: T.Type -> LT.Type
convertType "Int"          = LT.i32
convertType "Float"        = LT.double
convertType "Bool"         = LT.i1
convertType "Char"         = LT.i8
convertType "String"       = LT.ptr LT.i8
convertType "Unit"         = -- LT.NamedTypeReference "Unit"
  LT.StructureType False []
convertType (T.NameTy x) = error $ "unknown type: " ++ show x
convertType (T.TupleTy xs) =
  LT.StructureType False (map convertType xs)
convertType (T.FunTy params retTy) =
  LT.FunctionType (convertType retTy) (map convertType params) False
convertType (T.ClsTy _ _) = error "closure is not supported"
-- TODO: クロージャをLLVMでどのように扱うかを決める

getRef i = do
  m <- lift (gets _table)
  case Map.lookup i m of
    Nothing -> error $ show i ++ " is not found in " ++ show m
    Just x  -> return x

term o = do
  t <- lift (gets _term)
  o' <- o
  t o'

fromTypedID (TypedID i _) =
  fromString $ show (_name i) ++ "zi" ++ show (_uniq i)

char :: Applicative f => Integer -> f Operand
char = pure . ConstantOperand . C.Int 8

gcMalloc bytes = do
  f <- lift (fromJust . Map.lookup "GC_malloc" <$> gets _internal)
  bytes' <- int64 bytes
  call f [(bytes', [])]

genExpr e@(Var _)   = term (genExpr' e) `named` "var"
genExpr e@(Int _)   = term (genExpr' e) `named` "int"
genExpr e@(Float _) = term (genExpr' e) `named` "float"
genExpr e@(Bool _)  = term (genExpr' e) `named` "bool"
genExpr e@(Char _)  = term (genExpr' e) `named` "char"
genExpr e@(String _) = term (genExpr' e) `named` "string"
genExpr e@Unit = term (genExpr' e) `named` "unit"
genExpr (Tuple _) = error "tuple is not supported"
genExpr (TupleAccess _ _) = error "tuple is not supported"
genExpr (CallCls _ _) = error "closure is not supported"
genExpr e@(CallDir _ _) = term (genExpr' e) `named` "calldir"
genExpr e@(Let (ValDec _ _) _) = term (genExpr' e) `named` "let"
genExpr (Let ClsDec{} _) = error "closure is not supported"
genExpr e@If{} = term (genExpr' e) `named` "if"
genExpr e@(BinOp op _ _) = term (genExpr' e) `named` fromString (show op)

genExpr' (Var a)    = getRef a `named` "var"
genExpr' (Int i)    = int32 i `named` "int"
genExpr' (Float d)  = double d `named` "float"
genExpr' (Bool b)   = bit (if b then 1 else 0) `named` "bool"
genExpr' (Char c)   = char (toInteger . ord $ c) `named` "char"
genExpr' (String xs) = do
  p <- gcMalloc (toInteger $ length xs + 1) `named` "string"
  mapM_ (uncurry $ addChar p) (zip [0..] $ xs ++ ['\0'])
  return p
  where addChar p i c = do
          i' <- int32 i
          p' <- gep p [i'] `named` "tmp_char"
          c' <- char (toInteger . ord $ c)
          store p' 1 c'
genExpr' Unit       = (pure . ConstantOperand . C.Undef $ convertType "Unit") `named` "unit"
genExpr' (CallDir fn args) = do
  fn' <- getRef fn
  args' <- mapM (\a -> do a' <- getRef a; return (a', [])) args
  call fn' args'
genExpr' (Let (ValDec name val) e) = do
  val' <- genExpr' val `named` (fromString . show $ pretty name)
  addTable name val'
  genExpr' e
genExpr' (Let ClsDec{} _) = error "closure is not supported"
genExpr' (If c t f) = do
  c' <- getRef c
  r <- alloca (convertType (T.typeOf t)) Nothing 0 `named` "resultptr"
  (end, t', f') <- (,,) <$> freshName "end" <*> freshName "then" <*> freshName "else"
  condBr  c' t' f'
  backup <- lift (gets _term)
  lift (modify $ \s -> s { _term = \o -> store r 0 o >> br end })
  emitBlockStart t'; genExpr t
  emitBlockStart f'; genExpr f
  lift (modify $ \s -> s { _term = backup })
  emitBlockStart end
  load r 0
genExpr' (Tuple _) = error "tuple is not supported"
genExpr' (TupleAccess _ _) = error "tuple is not supported"
genExpr' (CallCls _ _) = error "closure is not supported"
genExpr' (BinOp op x y) = do
  let op' = case op of
        Add      -> add
        Sub      -> sub
        Mul      -> mul
        Div      -> sdiv
        FAdd     -> fadd
        FSub     -> fsub
        FMul     -> fmul
        FDiv     -> fdiv
        Mod      -> frem
        Eq ty -> case ty of
                   "Int"   -> icmp IP.EQ
                   "Float" -> fcmp FP.OEQ
                   "Bool"  -> icmp IP.EQ
                   "Char"  -> icmp IP.EQ
                   _       -> error $ show ty ++ " is not comparable"
        Neq ty -> case ty of
                   "Int"   -> icmp IP.NE
                   "Float" -> fcmp FP.ONE
                   "Bool"  -> icmp IP.NE
                   "Char"  -> icmp IP.NE
                   _       -> error $ show ty ++ " is not comparable"
        Lt ty -> case ty of
                   "Int"   -> icmp IP.SLT
                   "Float" -> fcmp FP.OLT
                   "Bool"  -> icmp IP.SLT
                   "Char"  -> icmp IP.SLT
                   _       -> error $ show ty ++ " is not comparable"
        Gt ty -> case ty of
                   "Int"   -> icmp IP.SGT
                   "Float" -> fcmp FP.OGT
                   "Bool"  -> icmp IP.SGT
                   "Char"  -> icmp IP.SGT
                   _       -> error $ show ty ++ " is not comparable"
        Le ty -> case ty of
                   "Int"   -> icmp IP.SLE
                   "Float" -> fcmp FP.OLE
                   "Bool"  -> icmp IP.SLE
                   "Char"  -> icmp IP.SLE
                   _       -> error $ show ty ++ " is not comparable"
        Ge ty -> case ty of
                   "Int"   -> icmp IP.SGE
                   "Float" -> fcmp FP.OGE
                   "Bool"  -> icmp IP.SGE
                   "Char"  -> icmp IP.SGE
                   _       -> error $ show ty ++ " is not comparable"
        And -> IRBuilder.and
        Or -> IRBuilder.or
  x' <- getRef x
  y' <- getRef y
  op' x' y'

genExDec (ExDec name str) = do
  let (argtys, retty) = case T.typeOf name of
                          (T.FunTy p r) -> (map convertType p, convertType r)
                          _ -> error $ show name ++ " is not callable"
  o <- extern (fromString str) argtys retty
  addTable name o

genFunDec :: FunDec TypedID -> GenDec ()
genFunDec (FunDec fn@(TypedID _ fnty) params [] body) = do
  let fn' = fromString (show (pretty fn))
  let params' = map (\(TypedID name ty) ->
                       (convertType ty, fromString (show (pretty name))))
                params
  let (TypedID _ (T.FunTy _ retty)) = fn
  let retty' = convertType retty
  let body' xs = do
        s <- lift get
        mapM_ (uncurry addTable) (zip params xs)
        genExpr body
  function fn' params' retty' body'
  return ()

genFunDec _ = error "closure is not supported"

genMain e =
  function "main" [] (convertType "Int") (\_ -> do genExpr' e `named` "main"; i <- int32 0; ret i)

genProgram ::
  Program TypedID -> GenDec ()
genProgram (Program fs es body) = do
  -- TODO: gc_mallocのexternを追加
  mapM_ genExDec es
  mapM_ addFunction fs
  mapM_ genFunDec fs
  _ <- genMain body
  return ()
  where addFunction (FunDec fn@(TypedID _ fnty) _ _ _) = do
          let fnop = ConstantOperand $ C.GlobalReference (convertType fnty) (fromString $ show $ pretty fn)
          addTable fn fnop


dumpCodeGen m =
  flip evalState (GenState Map.empty ret Map.empty) $ execModuleBuilderT emptyModuleBuilder
  (do addInternal "GC_malloc" (ConstantOperand
                                (C.GlobalReference
                                  (LT.FunctionType (LT.ptr LT.i8) [LT.i64] False)
                                  "GC_malloc"))
      m)