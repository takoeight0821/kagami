{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Malgo.Core.CodeGen
  ( CodeGen,
  )
where

import Control.Monad.Cont
import Control.Monad.Fix (MonadFix)
import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Short as BS
import Data.Char (ord)
import Data.Either (partitionEithers)
import Data.List.Extra (mconcatMap)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import LLVM.AST (Definition (..), Name, mkName)
import qualified LLVM.AST
import LLVM.AST.Constant (Constant (..))
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FloatingPointPredicate as FP
import LLVM.AST.Global
import qualified LLVM.AST.IntegerPredicate as IP
import LLVM.AST.Linkage (Linkage (External))
import LLVM.AST.Operand (Operand (..))
import LLVM.AST.Type hiding (double, void)
import qualified LLVM.AST.Type as LT
import LLVM.AST.Typed (typeOf)
import LLVM.IRBuilder hiding (globalStringPtr)
import Language.Malgo.IR.Core as Core
import qualified Language.Malgo.IR.Op as Op
import Language.Malgo.Id
import Language.Malgo.Monad
import Language.Malgo.Pass
import Language.Malgo.Prelude hiding (from, index, op, to)
import Language.Malgo.Pretty
import Language.Malgo.TypeRep.CType as CType

data CodeGen

instance Pass CodeGen (Program (Id CType)) [LLVM.AST.Definition] where
  passName = "GenLLVM"
  trans Program {topBinds, mainExp, topFuncs} = execModuleBuilderT emptyModuleBuilder $ do
    -- topBindsとtopFuncsのOprMapを作成
    bindEnv <-
      foldMapA ?? topBinds $
        \(x, _) -> do
          emitDefn $ LLVM.AST.GlobalDefinition LLVM.AST.globalVariableDefaults
          pure $
            Map.singleton x $
              ConstantOperand $ C.GlobalReference (ptr (convType $ cTypeOf x)) (toName x)
    let funcEnv =
          mconcatMap
            ?? topFuncs
            $ \(f, (ps, e)) ->
              Map.singleton f $
                ConstantOperand $ GlobalReference (ptr $ FunctionType (convType $ cTypeOf e) (map (convType . cTypeOf) ps) False) (toName f)
    runReaderT ?? (OprMap {_valueMap = mempty, _funcMap = funcEnv, _globalMap = bindEnv}) $
      Lazy.evalStateT ?? (mempty :: PrimMap) $ do
        traverse_ (\(f, (ps, body)) -> genFunc f ps body) topFuncs
        void $
          function "main" [] LT.i32 $ \_ -> do
            -- topBindsを初期化
            loadTopBinds topBinds
            gcInit <- findExt "GC_init" [] LT.void
            void $ call gcInit []
            genExp mainExp $ \_ -> ret (int32 0)

loadTopBinds ::
  ( MonadState PrimMap m,
    MonadModuleBuilder m,
    MonadIRBuilder m,
    MonadReader OprMap m,
    MonadUniq m,
    MonadFail m,
    MonadFix m
  ) =>
  [(Id CType, Obj (Id CType))] ->
  m ()
loadTopBinds xs = do
  traverse_ prepare xs
  env <- mconcat <$> traverse (uncurry genObj) xs
  OprMap {_globalMap} <- ask
  for_ (Map.toAscList env) $ \(i, opr) ->
    case _globalMap ^? ix i of
      Just globalAddr -> store globalAddr 0 opr
      Nothing -> bug Unreachable
  where
    prepare (name, Fun ps body) = do
      opr <- mallocType (StructureType False [ptr i8, ptr $ FunctionType (convType $ cTypeOf body) (ptr i8 : map (convType . cTypeOf) ps) False])
      OprMap {_globalMap} <- ask
      case _globalMap ^. at name of
        Just globalAddr -> store globalAddr 0 opr
        Nothing -> error $ show $ pPrint name <> " is not found"
    prepare _ = pure ()

-- 変数のMapとknown関数のMapを分割する
-- #7(https://github.com/takoeight0821/malgo/issues/7)のようなバグの早期検出が期待できる
data OprMap = OprMap
  { _valueMap :: Map (Id CType) Operand,
    _funcMap :: Map (Id CType) Operand,
    _globalMap :: Map (Id CType) Operand
  }

valueMap :: Lens' OprMap (Map (Id CType) Operand)
valueMap = lens _valueMap (\s a -> s {_valueMap = a})

-- funcMap :: Lens' OprMap (IdMap CType Operand)
-- funcMap = lens _funcMap (\s a -> s {_funcMap = a})

type PrimMap = Map Text Operand

convType :: CType -> Type
convType (ps :-> r) = ptr $ StructureType False [ptr i8, ptr $ FunctionType (convType r) (ptr i8 : map convType ps) False]
convType IntT = i64
convType FloatT = LT.double
convType CharT = i8
convType StringT = ptr i8
convType DataT {} = ptr i8
convType (SumT cs) =
  let size = maximum $ sizeofCon <$> toList cs
   in ptr (StructureType False [i64, if size == 0 then StructureType False [] else LT.VectorType size i8])
convType (ArrayT ty) = ptr $ StructureType False [ptr $ convType ty, i64]
convType VarT {} = ptr i8

sizeofCon :: Num a => Con -> a
sizeofCon (Con _ ts) = sum $ map sizeofCType ts

sizeofCType :: Num a => CType -> a
sizeofCType (_ :-> _) = 8
sizeofCType IntT = 8
sizeofCType FloatT = 8
sizeofCType CharT = 1
sizeofCType StringT = 8
sizeofCType DataT {} = 8
sizeofCType (SumT _) = 8
sizeofCType (ArrayT _) = 8
sizeofCType VarT {} = 8

findVar :: (MonadReader OprMap m, MonadIRBuilder m) => Id CType -> m Operand
findVar x = do
  OprMap {_valueMap = valueMap, _globalMap = globalMap} <- ask
  case valueMap ^. at x of
    Just x -> pure x
    Nothing -> case globalMap ^. at x of
      Just globalX -> load globalX 0
      Nothing -> error $ show $ pPrint x <> " is not found"

findFun :: MonadReader OprMap m => Id CType -> m Operand
findFun x = do
  OprMap {_funcMap = funcMap} <- ask
  case funcMap ^. at x of
    Just x -> pure x
    Nothing -> error $ show $ pPrint x <> " is not found"

findExt :: (MonadState PrimMap m, MonadModuleBuilder m) => Text -> [Type] -> Type -> m Operand
findExt x ps r = do
  env <- get
  case env ^. at x of
    Just x -> pure x
    Nothing -> do
      opr <- extern (LLVM.AST.mkName $ T.unpack x) ps r
      modify (at x ?~ opr)
      pure opr

mallocBytes ::
  ( MonadState PrimMap m,
    MonadModuleBuilder m,
    MonadIRBuilder m
  ) =>
  Operand ->
  Maybe Type ->
  m Operand
mallocBytes bytesOpr maybeType = do
  gcMalloc <- findExt "GC_malloc" [i64] (ptr i8)
  ptrOpr <- call gcMalloc [(bytesOpr, [])]
  case maybeType of
    Just t -> bitcast ptrOpr t
    Nothing -> pure ptrOpr

mallocType ::
  ( MonadState PrimMap m,
    MonadModuleBuilder m,
    MonadIRBuilder m
  ) =>
  Type ->
  m Operand
mallocType ty = mallocBytes (sizeof ty) (Just $ ptr ty)

toName :: Id a -> LLVM.AST.Name
toName x = LLVM.AST.mkName $ T.unpack (x ^. idName) <> show (x ^. idUniq)

genFunc ::
  ( MonadModuleBuilder m,
    MonadReader OprMap m,
    MonadState PrimMap m,
    MonadUniq m,
    MonadFix m,
    MonadFail m
  ) =>
  Id CType ->
  [Id CType] ->
  Exp (Id CType) ->
  m Operand
genFunc name params body = function funcName llvmParams retty $ \args ->
  local (over valueMap (Map.fromList (zip params args) <>)) $ genExp body ret
  where
    funcName = toName name
    llvmParams = map (\x -> (convType $ x ^. idMeta, ParameterName $ BS.toShort $ T.encodeUtf8 $ x ^. idName)) params
    retty = convType (cTypeOf body)

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
  Exp (Id CType) ->
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
genExp (PrimCall name (ps :-> r) xs) k = do
  primOpr <- findExt name (map convType ps) (convType r)
  xsOprs <- traverse genAtom xs
  k =<< call primOpr (map (,[]) xsOprs)
genExp (PrimCall _ t _) _ = error $ show $ pPrint t <> " is not fuction type"
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
      i1ToBool =<< case cTypeOf x of
        IntT -> icmp IP.EQ x' y'
        CharT -> icmp IP.EQ x' y'
        StringT -> icmp IP.EQ x' y'
        SumT _ -> icmp IP.EQ x' y'
        ArrayT _ -> icmp IP.EQ x' y'
        FloatT -> fcmp FP.OEQ x' y'
        _ -> bug Unreachable
    genOp Op.Neq = \x' y' ->
      i1ToBool =<< case cTypeOf x of
        IntT -> icmp IP.NE x' y'
        FloatT -> fcmp FP.ONE x' y'
        CharT -> icmp IP.NE x' y'
        StringT -> icmp IP.NE x' y'
        SumT _ -> icmp IP.NE x' y'
        ArrayT _ -> icmp IP.NE x' y'
        _ -> bug Unreachable
    genOp Op.Lt = \x' y' ->
      i1ToBool =<< case cTypeOf x of
        IntT -> icmp IP.SLT x' y'
        FloatT -> fcmp FP.OLT x' y'
        CharT -> icmp IP.ULT x' y'
        _ -> bug Unreachable
    genOp Op.Le = \x' y' ->
      i1ToBool =<< case cTypeOf x of
        IntT -> icmp IP.SLE x' y'
        FloatT -> fcmp FP.OLE x' y'
        CharT -> icmp IP.ULE x' y'
        _ -> bug Unreachable
    genOp Op.Gt = \x' y' ->
      i1ToBool =<< case cTypeOf x of
        IntT -> icmp IP.SGT x' y'
        FloatT -> fcmp FP.OGT x' y'
        CharT -> icmp IP.UGT x' y'
        _ -> bug Unreachable
    genOp Op.Ge = \x' y' ->
      i1ToBool =<< case cTypeOf x of
        IntT -> icmp IP.SGE x' y'
        FloatT -> fcmp FP.OGE x' y'
        CharT -> icmp IP.UGE x' y'
        _ -> bug Unreachable
    genOp _ = bug Unreachable
    i1ToBool i1opr = do
      boolVal <- mallocType (StructureType False [i64, StructureType False []])
      gepAndStore boolVal [int32 0, int32 0] =<< zext i1opr i64
      pure boolVal
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
  k (ConstantOperand (Undef (ptr $ StructureType False [i64, StructureType False []])))
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
                ptr $ FunctionType (convType $ cTypeOf body) (ptr i8 : map (convType . cTypeOf) ps) False
              ]
          )
    prepare _ = pure mempty
genExp (Match e cs) k = genExp e $ \eOpr -> do
  -- eOprの型がptr i8だったときに正しくタグを取り出すため、bitcastする
  -- TODO: genExpが正しい型の値を継続に渡すように変更する
  eOpr <- bitcast eOpr (convType $ cTypeOf e)
  case cTypeOf e of
    SumT union -> mdo
      br switchBlock
      (defs, labels) <- partitionEithers . toList <$> traverse (genUnpack eOpr union k) cs
      defaultLabel <- case defs of
        (l : _) -> pure l
        _ -> do
          l <- block
          unreachable
          pure l
      switchBlock <- block
      tagOpr <- gepAndLoad eOpr [int32 0, int32 0]
      switch tagOpr defaultLabel $ map (\(i, l) -> (C.Int 64 $ fromIntegral i, l)) labels
    _ -> case cs of
      (Bind x body :| _) -> local (over valueMap (at x ?~ eOpr)) $ genExp body k
      _ -> bug Unreachable
genExp (Cast ty x) k = do
  xOpr <- genAtom x
  k =<< bitcast xOpr (convType ty)

genUnpack ::
  ( MonadReader OprMap m,
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
  Case (Id CType) ->
  m (Either LLVM.AST.Name (Int, LLVM.AST.Name))
genUnpack scrutinee cs k = \case
  Bind x e -> do
    label <- block
    void $ local (over valueMap $ at x ?~ scrutinee) $ genExp e k
    pure $ Left label
  Unpack con vs e -> do
    label <- block
    let (tag, conType) = genCon cs con
    addr <- bitcast scrutinee (ptr $ StructureType False [i64, conType])
    payloadAddr <- gep addr [int32 0, int32 1]
    -- WRONG: payloadAddr <- (bitcast ?? ptr conType) =<< gep scrutinee [int32 0, int32 1]
    env <- ifoldMapA ?? vs $ \i v -> do
      vOpr <- gepAndLoad payloadAddr [int32 0, int32 $ fromIntegral i]
      pure $ Map.singleton v vOpr
    void $ local (over valueMap (env <>)) $ genExp e k
    pure $ Right (tag, label)

genAtom ::
  ( MonadReader OprMap m,
    MonadUniq m,
    MonadModuleBuilder m,
    MonadIRBuilder m
  ) =>
  Atom (Id CType) ->
  m Operand
genAtom (Var x) = findVar x
genAtom (Unboxed (Core.Int x)) = pure $ int64 x
genAtom (Unboxed (Core.Float x)) = pure $ double x
genAtom (Unboxed (Core.Char x)) = pure $ int8 $ toInteger $ ord x
genAtom (Unboxed (Core.String x)) = do
  i <- getUniq
  ConstantOperand <$> globalStringPtr x (mkName $ "str" <> show i)

genObj ::
  ( MonadReader OprMap m,
    MonadModuleBuilder m,
    MonadIRBuilder m,
    MonadState PrimMap m,
    MonadUniq m,
    MonadFail m,
    MonadFix m
  ) =>
  Id CType ->
  Obj (Id CType) ->
  m (Map (Id CType) Operand)
genObj funName (Fun ps e) = do
  name <- toName <$> newId () (funName ^. idName <> "_closure")
  func <- function name (map (,NoParameterName) psTypes) retType $ \case
    [] -> bug Unreachable
    (rawCapture : ps') -> do
      capture <- bitcast rawCapture (ptr capType)
      env <- ifoldMapA ?? fvs $ \i fv ->
        Map.singleton fv <$> gepAndLoad capture [int32 0, int32 $ fromIntegral i]
      let env' = Map.fromList $ zip ps ps'
      local (over valueMap ((env <> env') <>)) $ genExp e ret
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
    capType = StructureType False (map (convType . cTypeOf) fvs)
    psTypes = ptr i8 : map (convType . cTypeOf) ps
    retType = convType $ cTypeOf e
genObj name@(cTypeOf -> SumT cs) (Pack _ con@(Con _ ts) xs) = do
  addr <- mallocType (StructureType False [i64, StructureType False $ map convType ts])
  let tag = fromIntegral $ Set.findIndex con cs
  gepAndStore addr [int32 0, int32 0] (int64 tag)
  ifor_ xs $ \i x -> do
    xOpr <- genAtom x
    gepAndStore addr [int32 0, int32 1, int32 $ fromIntegral i] xOpr
  addr <- bitcast addr (convType $ SumT cs)
  pure $ Map.singleton name addr
genObj _ Pack {} = bug Unreachable
genObj x (Core.Array a n) = mdo
  sizeOpr <- mul (sizeof $ convType $ cTypeOf a) =<< genAtom n
  arrayOpr <- mallocBytes sizeOpr (Just $ ptr $ convType $ cTypeOf a)
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
  structOpr <- mallocType (StructureType False [ptr $ convType $ cTypeOf a, i64])
  gepAndStore structOpr [int32 0, int32 0] arrayOpr
  gepAndStore structOpr [int32 0, int32 1] =<< genAtom n
  pure $ Map.singleton x structOpr

genCon :: Set Con -> Con -> (Int, Type)
genCon cs con@(Con _ ts)
  | con `elem` cs = (Set.findIndex con cs, StructureType False (map convType ts))
  | otherwise = bug Unreachable

sizeof :: Type -> Operand
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

gepAndLoad :: (MonadIRBuilder m, MonadModuleBuilder m) => Operand -> [Operand] -> m Operand
gepAndLoad opr addrs = join $ load <$> gep opr addrs <*> pure 0

gepAndStore :: (MonadIRBuilder m, MonadModuleBuilder m) => Operand -> [Operand] -> Operand -> m ()
gepAndStore opr addrs val = join $ store <$> gep opr addrs <*> pure 0 <*> pure val