module Main where

import           Language.Malgo.Driver
import qualified Language.Malgo.Lexer       as Lexer
import qualified Language.Malgo.Parser      as Parser
import           Language.Malgo.Utils
import qualified Language.Malgo.Prelude as P

main :: IO ()
main = do
  opt <- parseOpt
  let file = _srcName opt
  contents <- readFile (P.toS file)
  let tokens = Lexer.lexing (P.toS file) contents
  let ast = case Parser.parseExpr <$> tokens of
        Left x  -> error $ show x
        Right x -> x
  obj <- compile ast opt

  if _compileOnly opt
    then return ()
    else do e <- eval obj
            case e of
              Left err -> error $ show $ P.pretty err
              Right result -> return (seq result ())
