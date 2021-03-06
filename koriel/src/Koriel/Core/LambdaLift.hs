{-# LANGUAGE TemplateHaskell #-}

module Koriel.Core.LambdaLift
  ( lambdalift,
  )
where

import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Koriel.Core.Flat
import Koriel.Core.Syntax
import Koriel.Core.Type
import Koriel.Id
import Koriel.MonadUniq
import Koriel.Prelude

data LambdaLiftState = LambdaLiftState
  { _funcs :: HashMap (Id Type) ([Id Type], Exp (Id Type)),
    _knowns :: HashSet (Id Type)
  }

makeLenses ''LambdaLiftState

lambdalift :: MonadIO m => UniqSupply -> Program (Id Type) -> m (Program (Id Type))
lambdalift us Program {..} =
  runReaderT ?? us $
    evalStateT ?? LambdaLiftState {_funcs = mempty, _knowns = HashSet.fromList $ map fst _topFuncs} $ do
      topFuncs <- traverse (\(f, (ps, e)) -> (f,) . (ps,) <$> llift e) _topFuncs
      funcs <>= HashMap.fromList topFuncs
      knowns <>= HashSet.fromList (map fst topFuncs)
      LambdaLiftState {_funcs} <- get
      traverseOf appProgram (pure . flat) $ Program _moduleName (HashMap.toList _funcs)

llift :: (MonadIO f, MonadState LambdaLiftState f, MonadReader UniqSupply f) => Exp (Id Type) -> f (Exp (Id Type))
llift (Call (Var f) xs) = do
  ks <- use knowns
  if f `elem` ks then pure $ CallDirect f xs else pure $ Call (Var f) xs
llift (Let [LocalDef n (Fun xs call@Call {})] e) = do
  call' <- llift call
  Let [LocalDef n (Fun xs call')] <$> llift e
llift (Let [LocalDef n o@(Fun _ ExtCall {})] e) = Let [LocalDef n o] <$> llift e
llift (Let [LocalDef n o@(Fun _ CallDirect {})] e) = Let [LocalDef n o] <$> llift e
llift (Let [LocalDef n (Fun as body)] e) = do
  backup <- get
  ks <- use knowns
  -- nがknownだと仮定してlambda liftする
  knowns . at n ?= ()
  body' <- llift body
  funcs . at n ?= (as, body')
  (e', _) <- localState $ llift e
  -- (Fun as body')の自由変数がknownsを除いてなく、e'の自由変数にnが含まれないならnはknown
  -- (Call n _)は(CallDirect n _)に変換されているので、nが値として使われているときのみ自由変数になる
  let fvs = HashSet.difference (freevars body') (ks <> HashSet.fromList as)
  if null fvs && n `notElem` freevars e'
    then llift e
    else do
      put backup
      body' <- llift body
      let fvs = HashSet.difference (freevars body') (ks <> HashSet.fromList as)
      newFun <- def (nameToString $ n ^. idName) (toList fvs <> as) body'
      Let [LocalDef n (Fun as (CallDirect newFun $ map Var $ toList fvs <> as))] <$> llift e
llift (Let ds e) = Let ds <$> llift e
llift (Match e cs) = Match <$> llift e <*> traverseOf (traversed . appCase) llift cs
llift e = pure e

def :: (MonadIO m, MonadState LambdaLiftState m, MonadReader env m, HasUniqSupply env) => String -> [Id Type] -> Exp (Id Type) -> m (Id Type)
def name xs e = do
  f <- newLocalId ("$raw_" <> name) (map typeOf xs :-> typeOf e)
  funcs . at f ?= (xs, e)
  pure f
