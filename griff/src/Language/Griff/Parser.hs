{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Griff.Parser where

import Control.Monad.Combinators.Expr
import Data.Functor (($>))
import qualified Data.Set as Set
import Data.Void
import Koriel.Prelude hiding
  ( many,
    some,
  )
import Language.Griff.Extension
import Language.Griff.Syntax
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void Text

parseGriff :: String -> Text -> Either (ParseErrorBundle Text Void) (String, [Decl (Griff 'Parse)])
parseGriff = parse pTopLevel

-- entry point
pTopLevel :: Parser (String, [Decl (Griff 'Parse)])
pTopLevel = do
  pKeyword "module"
  x <- pModuleName
  pOperator ";"
  (x,) <$> pDecl `sepEndBy` pOperator ";" <* eof

-- module name
pModuleName :: Parser String
pModuleName = some $ identLetter <|> char '.'

-- toplevel declaration
pDecl :: Parser (Decl (Griff 'Parse))
pDecl = pDataDef <|> pInfix <|> pForeign <|> try pScSig <|> pScDef

pDataDef :: Parser (Decl (Griff 'Parse))
pDataDef = label "toplevel type definition" $ do
  s <- getSourcePos
  void $ pKeyword "data"
  d <- upperIdent
  xs <- many lowerIdent
  void $ pOperator "="
  ts <- pConDef `sepBy` pOperator "|"
  pure $ DataDef s d xs ts
  where
    pConDef = (,) <$> upperIdent <*> many pSingleType

pInfix :: Parser (Decl (Griff 'Parse))
pInfix = label "infix declaration" $ do
  s <- getSourcePos
  a <-
    try (pKeyword "infixl" $> LeftA)
      <|> try (pKeyword "infixr" $> RightA)
      <|> (pKeyword "infix" $> NeutralA)
  i <- lexeme L.decimal
  x <- between (symbol "(") (symbol ")") operator
  pure $ Infix s a i x

pForeign :: Parser (Decl (Griff 'Parse))
pForeign = label "foreign import" $ do
  s <- getSourcePos
  pKeyword "foreign"
  pKeyword "import"
  x <- lowerIdent
  pOperator "::"
  Foreign s x <$> pType

pScSig :: Parser (Decl (Griff 'Parse))
pScSig =
  label "toplevel function signature" $
    ScSig
      <$> getSourcePos
      <*> (lowerIdent <|> between (symbol "(") (symbol ")") operator)
      <* pOperator "::"
      <*> pType

pScDef :: Parser (Decl (Griff 'Parse))
pScDef =
  label "toplevel function definition" $
    ScDef
      <$> getSourcePos
      <*> (lowerIdent <|> between (symbol "(") (symbol ")") operator)
      <*> many lowerIdent
      <* pOperator "="
      <*> pExp

-- Expressions

pExp :: Parser (Exp (Griff 'Parse))
pExp = pOpApp

pUnboxed :: Parser Unboxed
pUnboxed =
  label "unboxed literal" $
    try (Double <$> lexeme (L.float <* char '#'))
      <|> try (Float <$> lexeme (L.float <* string' "F#"))
      <|> try (Int32 <$> lexeme (L.decimal <* char '#'))
      <|> try (Int64 <$> lexeme (L.decimal <* string' "L#"))
      <|> try
        ( lexeme do
            x <- L.float <* notFollowedBy (char '#')
            registerFancyFailure (Set.singleton $ ErrorFail $ "unexpected '" <> show (x :: Double) <> "'\nMaybe you forgot '#'(Double#) or 'F#'(Float#)")
            pure undefined
        )
      <|> try
        ( lexeme do
            x <- L.decimal <* notFollowedBy (string "L#")
            registerFancyFailure (Set.singleton $ ErrorFail $ "unexpected '" <> show (x :: Int) <> "'\nMaybe you forgot '#'(Int32#) or 'L#'(Int64#)")
            pure undefined
        )
      <|> try (lexeme (Char <$> (between (char '\'') (char '\'') L.charLiteral <* char '#')))
      <|> lexeme do
        x <- between (char '\'') (char '\'') L.charLiteral <* notFollowedBy (char '#')
        registerFancyFailure (Set.singleton $ ErrorFail $ "unexpected '" <> show x <> "'\nMaybe you forgot '#'")
        pure undefined
      <|> try (lexeme (String <$> (char '"' *> manyTill L.charLiteral (char '"') <* char '#')))
      <|> lexeme do
        x <- char '"' *> manyTill L.charLiteral (char '"') <* notFollowedBy (char '#')
        registerFancyFailure (Set.singleton $ ErrorFail $ "unexpected '" <> show x <> "'\nMaybe you forgot '#'")
        pure undefined

pVariable :: Parser (Exp (Griff 'Parse))
pVariable = label "variable" $ Var <$> getSourcePos <*> lowerIdent

pConstructor :: Parser (Exp (Griff 'Parse))
pConstructor = label "constructor" $ Con <$> getSourcePos <*> upperIdent

pFun :: Parser (Exp (Griff 'Parse))
pFun =
  label "function literal" $
    between (symbol "{") (symbol "}") $
      Fn
        <$> getSourcePos
        <*> ( Clause
                <$> getSourcePos
                <*> (try (some pSinglePat <* pOperator "->") <|> pure [])
                <*> pExpInFn
            )
        `sepBy` pOperator "|"

pExpInFn :: Parser [Exp (Griff 'Parse)]
pExpInFn = pExp `sepEndBy` pOperator ";"

pSinglePat :: Parser (Pat (Griff 'Parse))
pSinglePat =
  VarP <$> getSourcePos <*> lowerIdent
    <|> ConP <$> getSourcePos <*> upperIdent <*> pure []
    <|> UnboxedP <$> getSourcePos <*> pUnboxed
    <|> between (symbol "(") (symbol ")") pPat

pPat :: Parser (Pat (Griff 'Parse))
pPat =
  label "pattern" $ try (ConP <$> getSourcePos <*> upperIdent <*> some pSinglePat) <|> pSinglePat

pTuple :: Parser (Exp (Griff 'Parse))
pTuple = label "tuple" $
  between (symbol "(") (symbol ")") $ do
    s <- getSourcePos
    x <- pExp
    pOperator ","
    xs <- pExp `sepBy` pOperator ","
    pure $ Tuple s (x : xs)

pUnit :: Parser (Exp (Griff 'Parse))
pUnit = between (symbol "(") (symbol ")") $ do
  s <- getSourcePos
  pure $ Tuple s []

pSingleExp' :: Parser (Exp (Griff 'Parse))
pSingleExp' =
  Unboxed <$> getSourcePos <*> pUnboxed
    <|> pVariable
    <|> pConstructor
    <|> try pUnit
    <|> try pTuple
    <|> pFun
    <|> between (symbol "(") (symbol ")") pExp

pSingleExp :: Parser (Exp (Griff 'Parse))
pSingleExp = try (Force <$> getSourcePos <*> pSingleExp' <* pOperator "!") <|> pSingleExp'

pApply :: Parser (Exp (Griff 'Parse))
pApply = do
  s <- getSourcePos
  f <- pSingleExp
  xs <- some pSingleExp
  pure $ foldl (Apply s) f xs

pTerm :: Parser (Exp (Griff 'Parse))
pTerm = try pApply <|> pSingleExp

pOpApp :: Parser (Exp (Griff 'Parse))
pOpApp = makeExprParser pTerm opTable
  where
    opTable =
      [ [ InfixL $ do
            s <- getSourcePos
            op <- operator
            pure $ \l r -> OpApp s op l r
        ]
      ]

-- Types

pType :: Parser (Type (Griff 'Parse))
pType = try pTyArr <|> pTyTerm

pTyVar :: Parser (Type (Griff 'Parse))
pTyVar = label "type variable" $ TyVar <$> getSourcePos <*> lowerIdent

pTyCon :: Parser (Type (Griff 'Parse))
pTyCon = label "type constructor" $ TyCon <$> getSourcePos <*> upperIdent

pTyTuple :: Parser (Type (Griff 'Parse))
pTyTuple = between (symbol "(") (symbol ")") $ do
  s <- getSourcePos
  x <- pType
  pOperator ","
  xs <- pType `sepBy` pOperator ","
  pure $ TyTuple s (x : xs)

pTyUnit :: Parser (Type (Griff 'Parse))
pTyUnit = between (symbol "(") (symbol ")") $ do
  s <- getSourcePos
  pure $ TyTuple s []

pTyLazy :: Parser (Type (Griff 'Parse))
pTyLazy = between (symbol "{") (symbol "}") $ TyLazy <$> getSourcePos <*> pType

pSingleType :: Parser (Type (Griff 'Parse))
pSingleType =
  pTyVar
    <|> pTyCon
    <|> pTyLazy
    <|> try pTyUnit
    <|> try pTyTuple
    <|> between (symbol "(") (symbol ")") pType

pTyApp :: Parser (Type (Griff 'Parse))
pTyApp = TyApp <$> getSourcePos <*> pSingleType <*> some pSingleType

pTyTerm :: Parser (Type (Griff 'Parse))
pTyTerm = try pTyApp <|> pSingleType

pTyArr :: Parser (Type (Griff 'Parse))
pTyArr = makeExprParser pTyTerm opTable
  where
    opTable =
      [ [ InfixR $ do
            s <- getSourcePos
            void $ pOperator "->"
            pure $ \l r -> TyArr s l r
        ]
      ]

-- combinators

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

identLetter :: Parser Char
identLetter = alphaNumChar <|> oneOf ("_#'" :: String)

opLetter :: Parser Char
opLetter = oneOf ("+-*/%=><:;|&!#." :: String)

pKeyword :: Text -> Parser ()
pKeyword keyword = void $ lexeme (string keyword <* notFollowedBy identLetter)

pOperator :: Text -> Parser ()
pOperator op = void $ lexeme (string op <* notFollowedBy opLetter)

reserved :: Parser ()
reserved =
  void $ choice $ map (try . pKeyword) ["module", "data", "infixl", "infixr", "infix", "foreign", "import"]

reservedOp :: Parser ()
reservedOp = void $ choice $ map (try . pOperator) ["=", "::", "|", "->", ";", ",", "!"]

lowerIdent :: Parser String
lowerIdent = label "lower identifier" $
  lexeme $ do
    notFollowedBy reserved
    (:) <$> (lowerChar <|> char '_') <*> many identLetter

upperIdent :: Parser String
upperIdent = label "upper identifier" $
  lexeme $ do
    notFollowedBy reserved
    (:) <$> upperChar <*> many identLetter

operator :: Parser String
operator = label "operator" $
  lexeme $ do
    notFollowedBy reservedOp
    some opLetter