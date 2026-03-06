{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Tiny.Parser where

import Control.Monad (guard)
import Data.Maybe (fromMaybe)
import Data.Void (Void)
import System.Exit (exitSuccess)
import Text.Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L

import Tiny.Syntax

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> getSourcePos <*> p

lexeme :: Parser a -> Parser a
lexeme = L.lexeme ws

symbol :: String -> Parser String
symbol s = lexeme (C.string s)

char :: Char -> Parser Char
char c = lexeme (C.char c)

parens :: Parser a -> Parser a
parens p = char '(' *> p <* char ')'

pArrow :: Parser String
pArrow = symbol "→" <|> symbol "->"

pTimes :: Parser String
pTimes = symbol "×" <|> symbol "*"

pSurd :: Parser String
pSurd = symbol "√" <|> symbol "v/"

keyword :: String -> Bool
keyword x =
  x == "let"
    || x == "inductive"
    || x == "magic"
    || x == "case"
    || x == "in"
    || x == "λ"
    || x == "U"
    || x == "T"
    || x == "t0"
    || x == "t1"
    || x == "rintro"
    || x == "relim"
    || x == "fst"
    || x == "snd"
    || x == "Path"

pIdent :: Parser Name
pIdent = try $ do
  x <- (:) <$> C.letterChar <*> many (C.alphaNumChar <|> C.char '_' <|> C.char '\'')
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = lexeme . try $ do
  C.string kw
  notFollowedBy (C.alphaNumChar <|> C.char '_' <|> C.char '\'')

pKeyList :: Parser [Raw]
pKeyList = do
  symbol "["
  keys <- sepBy1 pRaw (symbol ",")
  symbol "]"
  pure keys

pVar :: Parser Raw
pVar = do
  i <- pIdent
  keys <- fromMaybe [] <$> optional (try pKeyList)
  pure (RVar i keys)

pAtom :: Parser Raw
pAtom =
  withPos ((RU <$ pKeyword "U") <|> (RTiny <$ pKeyword "T") <|> (RTiny0 <$ pKeyword "t0") <|> (RTiny1 <$ pKeyword "t1") <|> pVar)
    <|> parens pRaw

pBinder :: Parser Name
pBinder = pIdent <|> symbol "_"

pSpine :: Parser Raw
pSpine = do
  h <- pAtom
  ts <- many (try pAtom)
  pure (foldl RApp h ts)

pPi :: Parser Raw
pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pArrow
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

pLam :: Parser Raw
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pRaw
  pure (foldr RLam t xs)

pSplit :: Parser Raw
pSplit = do
  char 'λ' <|> char '\\'
  symbol "["
  alts <- sepBy pCaseAlt (symbol ";")
  symbol "]"
  pure (RSplit alts)

pCaseAlt :: Parser RawCaseAlt
pCaseAlt = do
  c <- pIdent
  xs <- many pBinder
  char '.'
  body <- pRaw
  pure (RawCaseAlt c xs body)

pCase :: Parser Raw
pCase = do
  symbol "case"
  scrut <- pRaw
  motive <- optional (parens ((,) <$> pBinder <*> (char '.' *> pRaw)))
  symbol "["
  alts <- sepBy pCaseAlt (symbol ";")
  symbol "]"
  pure (RCase scrut motive alts)

pSg :: Parser Raw
pSg = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pTimes
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RSg x a) t xs) cod dom

pPair :: Parser Raw
pPair = do
  symbol "<"
  a <- pRaw
  symbol ","
  b <- pRaw
  symbol ">"
  pure (RPair a b)

pFst :: Parser Raw
pFst = do
  symbol "fst"
  t <- pRaw
  pure (RFst t)

pSnd :: Parser Raw
pSnd = do
  symbol "snd"
  t <- pRaw
  pure (RSnd t)

pPath :: Parser Raw
pPath = do
  symbol "Path"
  a0 <- pAtom
  a1 <- pAtom
  pure (RPath a0 a1)

pRoot :: Parser Raw
pRoot = do
  pSurd
  t <- pRaw
  pure (RRoot t)

pRootIntro :: Parser Raw
pRootIntro = do
  symbol "rintro"
  t <- pRaw
  pure (RRootIntro t)

pRootElim :: Parser Raw
pRootElim = do
  symbol "relim"
  xs <- pBinder
  char '.'
  t <- pRaw
  pure (RRootElim xs t)

funOrSpine :: Parser Raw
funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing ->
      optional pTimes >>= \case
        Nothing -> pure sp
        Just _ -> RSg "_" sp <$> pRaw
    Just _ -> RPi "_" sp <$> pRaw

pLet :: Parser Raw
pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pRaw
  symbol ":="
  t <- pRaw
  symbol ";"
  u <- pRaw
  pure $ RLet x a t u

typedArgGroup :: Parser [RawArg]
typedArgGroup = do
  (xs, a) <- parens ((,) <$> some pBinder <*> (char ':' *> pRaw))
  pure (fmap (`RawArg` a) xs)

pCtorField :: Parser [RawArg]
pCtorField =
  try typedArgGroup
    <|> ((: []) . RawArg "_" <$> pAtom)

pCtor :: Parser RawCtor
pCtor = do
  c <- pIdent
  fields <- concat <$> many pCtorField
  pure (RawCtor c fields)

pTopInd :: Parser RawDecl
pTopInd = do
  pos <- getSourcePos
  pKeyword "inductive"
  x <- pIdent
  params <- concat <$> many typedArgGroup
  symbol ":="
  ctors <- sepBy pCtor (symbol "|")
  symbol ";"
  pure (RTopInd pos x params ctors)

pTopMagic :: Parser RawDecl
pTopMagic = do
  pos <- getSourcePos
  pKeyword "magic"
  x <- pIdent
  char ':'
  a <- pRaw
  symbol ";"
  pure (RTopMagic pos x a)

pTopDef :: Parser RawDecl
pTopDef = do
  pos <- getSourcePos
  x <- pIdent
  args <- concat <$> many typedArgGroup
  mty <- optional (try (char ':' *> pRaw))
  symbol ":="
  t <- pRaw
  symbol ";"
  pure (RTopDef pos x args mty t)

pTopDecl :: Parser RawDecl
pTopDecl = try pTopInd <|> try pTopMagic <|> try pTopDef

pRaw :: Parser Raw
pRaw =
  withPos
    ( try pSplit
        <|> pLam
        <|> pCase
        <|> pPair
        <|> pFst
        <|> pSnd
        <|> pLet
        <|> pRoot
        <|> pRootIntro
        <|> pRootElim
        <|> pPath
        <|> try pPi
        <|> try pSg
        <|> funOrSpine
    )

pProgram :: Parser RawProgram
pProgram = RProgram <$> many pTopDecl <*> optional pRaw

pSrc :: Parser RawProgram
pSrc = ws *> pProgram <* eof

parseString :: String -> IO RawProgram
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t ->
      pure t

parseStdin :: IO (RawProgram, String)
parseStdin = do
  file <- getContents
  tm <- parseString file
  pure (tm, file)

parseFile :: String -> IO (RawProgram, String)
parseFile fn = do
  file <- readFile fn
  tm <- parseString file
  pure (tm, file)
