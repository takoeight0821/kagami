{-# LANGUAGE NoImplicitPrelude         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
module Language.Malgo.FrontEnd.LexerSpec where

import           Language.Malgo.FrontEnd.Lexer
import           Language.Malgo.FrontEnd.Loc
import           Language.Malgo.FrontEnd.Token
import           Test.Hspec
import           Universum

spec :: Spec
spec = describe "Lexer" $ do
  lextest "keywords"
    "type if then else let in rec true false forall"
    [TYPE, IF, THEN, ELSE, LET, IN, REC, TRUE, FALSE, FORALL]
  lextest "operators"
    "+ - * / % +. -. *. /. == /= < > <= >= & |"
    [ PLUS, MINUS, ASTERISK, SLASH, PERCENT, PLUS_DOT, MINUS_DOT
    , ASTERISK_DOT, SLASH_DOT, EQ_OP, NEQ_OP, LT_OP, GT_OP, LE_OP
    , GE_OP, AND_OP, OR_OP]

  lextest "annotation"
    "f : forall a. a -> a"
    [ID "f", COLON, FORALL, ID "a", DOT, ID "a", ARROW, ID "a"]
  lextest "function definition"
    "f x = x"
    [ID "f", ID "x", EQUAL, ID "x"]
  lextest "type alias definition"
    "type T = Array Int"
    [TYPE, LID "T", EQUAL, LID "Array", LID "Int"]

  lextest "literal" "42 3.14 true false 'c' \"str\"" [INT 42, FLOAT 3.14, TRUE, FALSE, CHAR 'c', STRING "str"]

  lextest "arithmetic expression"
    "4 * 10 + 2" [INT 4, ASTERISK, INT 10, PLUS, INT 2]
  lextest "negate"
    "-43 - -1" [MINUS, INT 43, MINUS, MINUS, INT 1]
  lextest "x - 1" "x - 1" [ID "x", MINUS, INT 1]
  lextest "x - -1" "x - -1" [ID "x", MINUS, MINUS, INT 1]
  lextest "3.0 +. 0.14" "3.0 +. 0.14" [FLOAT 3.0, PLUS_DOT, FLOAT 0.14]

  lextest "simple apply" "f x" [ID "f", ID "x"]
  lextest "multiple arguments" "f x y" [ID "f", ID "x", ID "y"]
  lextest "function call and arithmetic expression"
    "f 1 + 2" [ID "f", INT 1, PLUS, INT 2]

ss :: SrcSpan
ss = SrcSpan "<test>" 0 0 0 0

tok :: Tag -> Token
tok = Loc ss

toks :: [Tag] -> Either a [Token]
toks = Right . map tok

lextest :: String -> Text -> [Tag] -> SpecWith ()
lextest desc str ts = do
  t <- lex "<test>" str
  it desc $ t `shouldBe` toks ts
