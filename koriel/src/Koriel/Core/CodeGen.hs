{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- |
-- LLVM IRの生成
module Koriel.Core.CodeGen
  ( codeGen,
  )
where

import Control.Monad.Fix (MonadFix)
import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Short as BS
import Data.Char (ord)
import Data.Either (partitionEithers)
import Data.List.Extra (headDef, mconcatMap)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String.Conversions
import GHC.Float (castDoubleToWord64, castFloatToWord32)
import Koriel.Core.Core as Core
import qualified Koriel.Core.Op as Op
import Koriel.Core.Type as C
import Koriel.Id
import Koriel.MonadUniq
import Koriel.Prelude
import Koriel.Pretty
import LLVM.AST
  ( Definition (..),
    Name,
    mkName,
  )
import LLVM.AST.Constant (Constant (..))
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FloatingPointPredicate as FP
import LLVM.AST.Global
import qualified LLVM.AST.IntegerPredicate as IP
import LLVM.AST.Linkage (Linkage (External, Internal))
import LLVM.AST.Operand (Operand (..))
import LLVM.AST.Type hiding
  ( double,
    void,
  )
import qualified LLVM.AST.Type as LT
import LLVM.AST.Typed (typeOf)
import LLVM.IRBuilder hiding (globalStringPtr)

type PrimMap = Map String Operand

-- 変数のMapとknown関数のMapを分割する
-- #7(https://github.com/takoeight0821/malgo/issues/7)のようなバグの早期検出が期待できる
data OprMap = OprMap
  { _valueMap :: Map (Id C.Type) Operand,
    _funcMap :: Map (Id C.Type) Operand
  }

makeLenses ''OprMap

codeGen :: (MonadUniq m, MonadFix m, MonadFail m) => Program (Id C.Type) -> m [Definition]
codeGen Program {topFuncs} = execModuleBuilderT emptyModuleBuilder $ do
  -- topFuncsのOprMapを作成
  let funcEnv = mconcatMap ?? topFuncs $ \(f, (ps, e)) ->
        Map.singleton f $
          ConstantOperand $
            GlobalReference
              (ptr $ FunctionType (convType $ C.typeOf e) (map (convType . C.typeOf) ps) False)
              (toName f)
  runReaderT
    ?? (OprMap {_valueMap = mempty, _funcMap = funcEnv})
    $ Lazy.evalStateT
      ?? (mempty :: PrimMap)
      $ do
        traverse_ (\(f, (ps, body)) -> genFunc f ps body) topFuncs

convType :: C.Type -> LT.Type
convType (ps :-> r) =
  ptr $
    StructureType False [ptr i8, ptr $ FunctionType (convType r) (ptr i8 : map convType ps) False]
convType Int32T = i32
convType Int64T = i64
convType FloatT = LT.float
convType DoubleT = LT.double
convType CharT = i8
convType StringT = ptr i8
convType BoolT = i8
convType DataT {} = ptr i8
convType (SumT cs) =
  let size = maximum $ sizeofCon <$> toList cs
   in ptr
        ( StructureType
            False
            [i8, if size == 0 then StructureType False [] else LT.VectorType size i8]
        )
convType (ArrayT ty) = ptr $ StructureType False [ptr $ convType ty, i64]
convType (PtrT ty) = ptr $ convType ty
convType AnyT = ptr i8
convType VoidT = LT.void

sizeofCon :: Num a => Con -> a
sizeofCon (Con _ ts) = sum $ map sizeofType ts

sizeofType :: Num a => C.Type -> a
sizeofType (_ :-> _) = 8
sizeofType Int32T = 4
sizeofType Int64T = 8
sizeofType FloatT = 4
sizeofType DoubleT = 8
sizeofType CharT = 1
sizeofType StringT = 8
sizeofType BoolT = 1
sizeofType DataT {} = 8
sizeofType (SumT _) = 8
sizeofType (ArrayT _) = 8
sizeofType (PtrT _) = 8
sizeofType AnyT = 8
sizeofType VoidT = 0

findVar :: (MonadReader OprMap m, MonadIRBuilder m) => Id C.Type -> m Operand
findVar x = do
  mopr <- view $ valueMap . at x
  case mopr of
    Just opr -> pure opr
    Nothing -> error $ show $ pPrint x <> " is not found"

findFun :: (MonadReader OprMap m, MonadState PrimMap m, MonadModuleBuilder m) => Id C.Type -> m Operand
findFun x = do
  mopr <- view $ funcMap . at x
  case mopr of
    Just opr -> pure opr
    Nothing ->
      case C.typeOf x of
        ps :-> r -> findExt (show $ pPrint x) (map convType ps) (convType r)
        _ -> error $ show $ pPrint x <> " is not found"

-- まだ生成していない外部関数を呼び出そうとしたら、externする
-- すでにexternしている場合は、そのOperandを返す
findExt :: (MonadState PrimMap m, MonadModuleBuilder m) => String -> [LT.Type] -> LT.Type -> m Operand
findExt x ps r =
  use (at x) >>= \case
    Just x -> pure x
    Nothing -> (at x <?=) =<< extern (LLVM.AST.mkName x) ps r

mallocBytes ::
  (MonadState PrimMap m, MonadModuleBuilder m, MonadIRBuilder m) =>
  Operand ->
  Maybe LT.Type ->
  m Operand
mallocBytes bytesOpr maybeType = do
  gcMalloc <- findExt "GC_malloc" [i64] (ptr i8)
  ptrOpr <- call gcMalloc [(bytesOpr, [])]
  case maybeType of
    Just t -> bitcast ptrOpr t
    Nothing -> pure ptrOpr

mallocType :: (MonadState PrimMap m, MonadModuleBuilder m, MonadIRBuilder m) => LT.Type -> m Operand
mallocType ty = mallocBytes (sizeof ty) (Just $ ptr ty)

toName :: Pretty a => Id a -> LLVM.AST.Name
toName x = LLVM.AST.mkName $ show $ pPrint x

-- generate code for a 'known' function
genFunc ::
  ( MonadModuleBuilder m,
    MonadReader OprMap m,
    MonadState PrimMap m,
    MonadUniq m,
    MonadFix m,
    MonadFail m
  ) =>
  Id C.Type ->
  [Id C.Type] ->
  Exp (Id C.Type) ->
  m Operand
genFunc name params body
  | name ^. idIsExternal =
    function funcName llvmParams retty $ \args -> local (over valueMap (Map.fromList (zip params args) <>)) $ genExp body ret
  | otherwise =
    internalFunction funcName llvmParams retty $ \args -> local (over valueMap (Map.fromList (zip params args) <>)) $ genExp body ret
  where
    funcName = toName name
    llvmParams =
      map
        (\x -> (convType $ x ^. idMeta, ParameterName $ BS.toShort $ convertString $ x ^. idName))
        params
    retty = convType (C.typeOf body)

-- genUnpackでコード生成しつつラベルを返すため、CPSにしている
genExp ::
  ( MonadReader OprMap m,
    MonadUniq m,
    MonadState PrimMap m,
    MonadIRBuilder m,
    MonadModuleBuilder m,
    MonadFail m,
    MonadFix m
  ) =>
  Exp (Id C.Type) ->
  (Operand -> m ()) ->
  m ()
genExp (Atom x) k = k =<< genAtom x
genExp (Call f xs) k = do
  fOpr <- genAtom f
  captureOpr <- gepAndLoad fOpr [int32 0, int32 0]
  funcOpr <- gepAndLoad fOpr [int32 0, int32 1]
  xsOprs <- traverse genAtom xs
  k =<< call funcOpr (map (,[]) $ captureOpr : xsOprs)
genExp (CallDirect f xs) k = do
  fOpr <- findFun f
  xsOprs <- traverse genAtom xs
  k =<< call fOpr (map (,[]) xsOprs)
genExp (ExtCall name (ps :-> r) xs) k = do
  primOpr <- findExt name (map convType ps) (convType r)
  xsOprs <- traverse genAtom xs
  k =<< call primOpr (map (,[]) xsOprs)
genExp (ExtCall _ t _) _ = error $ show $ pPrint t <> " is not fuction type"
genExp (BinOp o x y) k = k =<< join (genOp o <$> genAtom x <*> genAtom y)
  where
    genOp Op.Add = add
    genOp Op.Sub = sub
    genOp Op.Mul = mul
    genOp Op.Div = sdiv
    genOp Op.Mod = srem
    genOp Op.FAdd = fadd
    genOp Op.FSub = fsub
    genOp Op.FMul = fmul
    genOp Op.FDiv = fdiv
    genOp Op.Eq = \x' y' ->
      i1ToBool =<< case C.typeOf x of
        Int32T -> icmp IP.EQ x' y'
        Int64T -> icmp IP.EQ x' y'
        FloatT -> fcmp FP.OEQ x' y'
        DoubleT -> fcmp FP.OEQ x' y'
        CharT -> icmp IP.EQ x' y'
        StringT -> icmp IP.EQ x' y'
        BoolT -> icmp IP.EQ x' y'
        SumT _ -> icmp IP.EQ x' y'
        ArrayT _ -> icmp IP.EQ x' y'
        _ -> bug Unreachable
    genOp Op.Neq = \x' y' ->
      i1ToBool =<< case C.typeOf x of
        Int32T -> icmp IP.NE x' y'
        Int64T -> icmp IP.NE x' y'
        FloatT -> fcmp FP.ONE x' y'
        DoubleT -> fcmp FP.ONE x' y'
        CharT -> icmp IP.NE x' y'
        StringT -> icmp IP.NE x' y'
        BoolT -> icmp IP.NE x' y'
        SumT _ -> icmp IP.NE x' y'
        ArrayT _ -> icmp IP.NE x' y'
        _ -> bug Unreachable
    genOp Op.Lt = \x' y' ->
      i1ToBool =<< case C.typeOf x of
        Int32T -> icmp IP.SLT x' y'
        Int64T -> icmp IP.SLT x' y'
        FloatT -> fcmp FP.OLT x' y'
        DoubleT -> fcmp FP.OLT x' y'
        CharT -> icmp IP.ULT x' y'
        _ -> bug Unreachable
    genOp Op.Le = \x' y' ->
      i1ToBool =<< case C.typeOf x of
        Int32T -> icmp IP.SLE x' y'
        Int64T -> icmp IP.SLE x' y'
        FloatT -> fcmp FP.OLE x' y'
        DoubleT -> fcmp FP.OLE x' y'
        CharT -> icmp IP.ULE x' y'
        _ -> bug Unreachable
    genOp Op.Gt = \x' y' ->
      i1ToBool =<< case C.typeOf x of
        Int32T -> icmp IP.SGT x' y'
        Int64T -> icmp IP.SGT x' y'
        FloatT -> fcmp FP.OGT x' y'
        DoubleT -> fcmp FP.OGT x' y'
        CharT -> icmp IP.UGT x' y'
        _ -> bug Unreachable
    genOp Op.Ge = \x' y' ->
      i1ToBool =<< case C.typeOf x of
        Int32T -> icmp IP.SGE x' y'
        Int64T -> icmp IP.SGE x' y'
        FloatT -> fcmp FP.OGE x' y'
        DoubleT -> fcmp FP.OGE x' y'
        CharT -> icmp IP.UGE x' y'
        _ -> bug Unreachable
    genOp Op.And =
      LLVM.IRBuilder.and
    genOp Op.Or =
      LLVM.IRBuilder.or
    i1ToBool i1opr =
      zext i1opr i8
genExp (ArrayRead a i) k = do
  aOpr <- genAtom a
  iOpr <- genAtom i
  arrOpr <- gepAndLoad aOpr [int32 0, int32 0]
  k =<< gepAndLoad arrOpr [iOpr]
genExp (ArrayWrite a i v) k = do
  aOpr <- genAtom a
  iOpr <- genAtom i
  vOpr <- genAtom v
  arrOpr <- gepAndLoad aOpr [int32 0, int32 0]
  gepAndStore arrOpr [iOpr] vOpr
  k (ConstantOperand (Undef (ptr $ StructureType False [i8, StructureType False []])))
genExp (Let xs e) k = do
  env <- foldMapA prepare xs
  env <- local (over valueMap (env <>)) $ mconcat <$> traverse (uncurry genObj) xs
  local (over valueMap (env <>)) $ genExp e k
  where
    prepare (name, Fun ps body) =
      Map.singleton name
        <$> mallocType
          ( StructureType
              False
              [ ptr i8,
                ptr $ FunctionType (convType $ C.typeOf body) (ptr i8 : map (convType . C.typeOf) ps) False
              ]
          )
    prepare _ = pure mempty
genExp (Match e (Bind _ body :| _)) k | C.typeOf e == VoidT = genExp e $ \_ -> genExp body k
genExp (Match e (Bind x body :| _)) k = genExp e $ \eOpr -> do
  eOpr <- bitcast eOpr (convType $ C.typeOf e)
  local (over valueMap (at x ?~ eOpr)) (genExp body k)
genExp (Match e cs) k
  | C.typeOf e == VoidT = error "VoidT is not able to bind to variable."
  | otherwise = genExp e $ \eOpr -> mdo
    -- eOprの型がptr i8だったときに正しくタグを取り出すため、bitcastする
    -- TODO: genExpが正しい型の値を継続に渡すように変更する
    eOpr' <- bitcast eOpr (convType $ C.typeOf e)
    br switchBlock
    -- 各ケースのコードとラベルを生成する
    -- switch用のタグがある場合は Right (タグ, ラベル) を、ない場合は Left タグ を返す
    (defs, labels) <- partitionEithers . toList <$> traverse (genCase eOpr' (fromMaybe mempty $ e ^? to C.typeOf . _SumT) k) cs
    -- defsの先頭を取り出し、switchのデフォルトケースとする
    -- defsが空の場合、デフォルトケースはunreachableにジャンプする
    defaultLabel <- headDef (block >>= \l -> unreachable >> pure l) $ map pure defs
    switchBlock <- block
    tagOpr <- case C.typeOf e of
      SumT _ -> gepAndLoad eOpr' [int32 0, int32 0]
      _ -> pure eOpr'
    switch tagOpr defaultLabel labels
genExp (Cast ty x) k = do
  xOpr <- genAtom x
  k =<< bitcast xOpr (convType ty)
genExp (Error _) _ = unreachable

genCase ::
  ( HasCallStack,
    MonadReader OprMap m,
    MonadUniq m,
    MonadModuleBuilder m,
    MonadState PrimMap m,
    MonadIRBuilder m,
    MonadFail m,
    MonadFix m
  ) =>
  Operand ->
  Set Con ->
  (Operand -> m ()) ->
  Case (Id C.Type) ->
  m (Either LLVM.AST.Name (Constant, LLVM.AST.Name))
genCase scrutinee cs k = \case
  Bind x e -> do
    label <- block
    void $ local (over valueMap $ at x ?~ scrutinee) $ genExp e k
    pure $ Left label
  Switch u e -> do
    ConstantOperand u' <- genAtom $ Unboxed u
    label <- block
    genExp e k
    pure $ Right (u', label)
  Unpack con vs e -> do
    label <- block
    let (tag, conType) = genCon cs con
    addr <- bitcast scrutinee (ptr $ StructureType False [i8, conType])
    payloadAddr <- gep addr [int32 0, int32 1]
    -- WRONG: payloadAddr <- (bitcast ?? ptr conType) =<< gep scrutinee [int32 0, int32 1]
    env <- ifoldMapA ?? vs $ \i v -> do
      vOpr <- gepAndLoad payloadAddr [int32 0, int32 $ fromIntegral i]
      pure $ Map.singleton v vOpr
    void $ local (over valueMap (env <>)) $ genExp e k
    pure $ Right (C.Int 8 tag, label)

genAtom ::
  (MonadReader OprMap m, MonadUniq m, MonadModuleBuilder m, MonadIRBuilder m) =>
  Atom (Id C.Type) ->
  m Operand
genAtom (Var x) = findVar x
genAtom (Unboxed (Core.Int32 x)) = pure $ int32 x
genAtom (Unboxed (Core.Int64 x)) = pure $ int64 x
-- Ref: https://github.com/llvm-hs/llvm-hs/issues/4
genAtom (Unboxed (Core.Float x)) = pure $ ConstantOperand $ C.BitCast (C.Int 32 $ toInteger $ castFloatToWord32 x) LT.float
genAtom (Unboxed (Core.Double x)) = pure $ ConstantOperand $ C.BitCast (C.Int 64 $ toInteger $ castDoubleToWord64 x) LT.double
genAtom (Unboxed (Core.Char x)) = pure $ int8 $ toInteger $ ord x
genAtom (Unboxed (Core.String x)) = do
  i <- getUniq
  ConstantOperand <$> globalStringPtr x (mkName $ "str" <> show i)
genAtom (Unboxed (Core.Bool True)) = pure $ int8 1
genAtom (Unboxed (Core.Bool False)) = pure $ int8 0

genObj ::
  ( MonadReader OprMap m,
    MonadModuleBuilder m,
    MonadIRBuilder m,
    MonadState PrimMap m,
    MonadUniq m,
    MonadFail m,
    MonadFix m
  ) =>
  Id C.Type ->
  Obj (Id C.Type) ->
  m (Map (Id C.Type) Operand)
genObj funName (Fun ps e) = do
  -- クロージャの元になる関数を生成する
  name <- toName <$> newTopLevelId (funName ^. idName <> "_closure") ()
  func <- internalFunction name (map (,NoParameterName) psTypes) retType $ \case
    [] -> bug Unreachable
    (rawCapture : ps') -> do
      -- キャプチャした変数が詰まっている構造体を展開する
      capture <- bitcast rawCapture (ptr capType)
      env <- ifoldMapA ?? fvs $ \i fv ->
        Map.singleton fv <$> gepAndLoad capture [int32 0, int32 $ fromIntegral i]
      local (over valueMap ((env <> Map.fromList (zip ps ps')) <>)) $ genExp e ret
  -- キャプチャされる変数を構造体に詰める
  capture <- mallocType capType
  ifor_ fvs $ \i fv -> do
    fvOpr <- findVar fv
    gepAndStore capture [int32 0, int32 $ fromIntegral i] fvOpr
  closAddr <- findVar funName
  gepAndStore closAddr [int32 0, int32 0] =<< bitcast capture (ptr i8)
  gepAndStore closAddr [int32 0, int32 1] func
  pure $ Map.singleton funName closAddr
  where
    fvs = toList $ freevars (Fun ps e)
    -- キャプチャされる変数を詰める構造体の型
    capType = StructureType False (map (convType . C.typeOf) fvs)
    psTypes = ptr i8 : map (convType . C.typeOf) ps
    retType = convType $ C.typeOf e
genObj name@(C.typeOf -> SumT cs) (Pack _ con@(Con _ ts) xs) = do
  addr <- mallocType (StructureType False [i8, StructureType False $ map convType ts])
  -- タグの書き込み
  gepAndStore addr [int32 0, int32 0] (int8 $ findIndex con cs)
  -- 引数の書き込み
  ifor_ xs $ \i x ->
    gepAndStore addr [int32 0, int32 1, int32 $ fromIntegral i] =<< genAtom x
  -- nameの型にキャスト
  Map.singleton name <$> bitcast addr (convType $ SumT cs)
genObj _ Pack {} = bug Unreachable
genObj x (Core.Array a n) = mdo
  sizeOpr <- mul (sizeof $ convType $ C.typeOf a) =<< genAtom n
  arrayOpr <- mallocBytes sizeOpr (Just $ ptr $ convType $ C.typeOf a)
  -- for (i64 i = 0;
  iPtr <- alloca i64 Nothing 0
  store iPtr 0 (int64 0)
  br condLabel
  -- cond: i < n;
  condLabel <- block
  iOpr <- load iPtr 0
  cond <- icmp IP.SLT iOpr =<< genAtom n
  condBr cond bodyLabel endLabel
  -- body: valueOpr[iOpr] <- genAtom a
  bodyLabel <- block
  iOpr' <- load iPtr 0
  gepAndStore arrayOpr [iOpr'] =<< genAtom a
  store iPtr 0 =<< add iOpr (int64 1)
  br condLabel
  endLabel <- block
  -- return array struct
  structOpr <- mallocType (StructureType False [ptr $ convType $ C.typeOf a, i64])
  gepAndStore structOpr [int32 0, int32 0] arrayOpr
  gepAndStore structOpr [int32 0, int32 1] =<< genAtom n
  pure $ Map.singleton x structOpr

genCon :: HasCallStack => Set Con -> Con -> (Integer, LT.Type)
genCon cs con@(Con _ ts)
  | con `elem` cs = (findIndex con cs, StructureType False (map convType ts))
  | otherwise = errorDoc $ pPrint con <+> "is not in" <+> pPrint (Set.toList cs)

findIndex :: (HasCallStack, Ord a, Pretty a) => a -> Set a -> Integer
findIndex con cs = case Set.lookupIndex con cs of
  Just i -> fromIntegral i
  Nothing -> errorDoc $ pPrint con <+> "is not in" <+> pPrint (Set.toList cs)

sizeof :: LT.Type -> Operand
sizeof ty = ConstantOperand $ C.PtrToInt szPtr LT.i64
  where
    ptrType = LT.ptr ty
    nullPtr = C.IntToPtr (C.Int 32 0) ptrType
    szPtr = C.GetElementPtr True nullPtr [C.Int 32 1]

globalStringPtr :: MonadModuleBuilder m => String -> Name -> m C.Constant
globalStringPtr str nm = do
  let utf8Vals = map toInteger $ BL.unpack $ B.toLazyByteString $ B.stringUtf8 str
      llvmVals = map (C.Int 8) (utf8Vals ++ [0])
      char = IntegerType 8
      charArray = C.Array char llvmVals
      ty = LLVM.AST.Typed.typeOf charArray
  emitDefn $
    GlobalDefinition
      globalVariableDefaults
        { name = nm,
          LLVM.AST.Global.type' = ty,
          linkage = External,
          isConstant = True,
          initializer = Just charArray,
          unnamedAddr = Just GlobalAddr
        }
  pure $ C.GetElementPtr True (C.GlobalReference (ptr ty) nm) [C.Int 32 0, C.Int 32 0]

gepAndLoad ::
  (HasCallStack, MonadIRBuilder m, MonadModuleBuilder m) =>
  Operand ->
  [Operand] ->
  m Operand
gepAndLoad opr addrs = join $ load <$> gep opr addrs <*> pure 0

gepAndStore ::
  (HasCallStack, MonadIRBuilder m, MonadModuleBuilder m) =>
  Operand ->
  [Operand] ->
  Operand ->
  m ()
gepAndStore opr addrs val = join $ store <$> gep opr addrs <*> pure 0 <*> pure val

internalFunction ::
  MonadModuleBuilder m =>
  -- | Function name
  Name ->
  -- | Parameter types and name suggestions
  [(LT.Type, ParameterName)] ->
  -- | Return type
  LT.Type ->
  -- | Function body builder
  ([Operand] -> IRBuilderT m ()) ->
  m Operand
internalFunction label argtys retty body = do
  let tys = fst <$> argtys
  (paramNames, blocks) <- runIRBuilderT emptyIRBuilder $ do
    paramNames <- for argtys $ \case
      (_, NoParameterName) -> fresh
      (_, ParameterName p) -> fresh `named` p
    body $ zipWith LocalReference tys paramNames
    return paramNames
  let def =
        GlobalDefinition
          functionDefaults
            { name = label,
              linkage = Internal,
              parameters = (zipWith (\ty nm -> Parameter ty nm []) tys paramNames, False),
              returnType = retty,
              basicBlocks = blocks
            }
      funty = ptr $ FunctionType retty (fst <$> argtys) False
  emitDefn def
  pure $ ConstantOperand $ C.GlobalReference funty label
