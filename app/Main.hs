module Main where

import           Control.Arrow         ((&&&))
import           Control.Monad.State
import qualified Language.Malgo.HIR    as HIR
-- import qualified Language.Malgo.KNormal as KNormal
import qualified Language.Malgo.Parser as Parser
import qualified Language.Malgo.Syntax as Syntax
import qualified Language.Malgo.Typing as Typing
import           System.Environment    (getArgs)
import qualified Text.Parsec.String    as P
import qualified Text.PrettyPrint      as Pretty
main :: IO ()
main = do
  args <- getArgs
  let file = head args
  result <- P.parseFromFile Parser.parseToplevel file
  case result of
    Left err  -> print err
    Right ast -> do
      putStrLn "Format:"
      print $ Pretty.sep (map Syntax.prettyDecl ast)
      putStrLn "AST:"
      print ast

      putStrLn "Typed AST(HIR 'Typed):"
      let typedAst = Typing.typing ast
      case typedAst of
        Right xs -> print $ xs
        Left x   -> putStrLn $ "typing error: " ++ x

      -- putStrLn "KNormalized AST(HIR 'KNormal):"
      -- let kAst = case typedAst of
      --              Right tAst -> Right $ map (fst . KNormal.trans) tAst
      --              Left x     -> Left x
      -- case kAst of
      --   Right xs -> print $ map HIR.prettyHIR xs
      --   Left _   -> return ();
