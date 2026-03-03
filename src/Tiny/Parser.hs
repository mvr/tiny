{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Tiny.Parser where

import Control.Monad (guard)
import Data.Char (isAlphaNum)
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
    || x == "in"
    || x == "λ"
    || x == "U"
    || x == "T"
    || x == "rintro"
    || x == "relim"
    || x == "fst"
    || x == "snd"
    || x == "Path"

pIdent :: Parser Name
pIdent = try $ do
  x <- (:) <$> C.letterChar <*> many (C.alphaNumChar <|> char '_')
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pKeyList :: Parser [Raw]
pKeyList = do
  symbol "["
  keys <- sepBy pRaw (symbol ",")
  symbol "]"
  pure keys

pVar :: Parser Raw
pVar = do
  i <- pIdent
  keys <- fromMaybe [] <$> optional pKeyList
  pure (RVar i keys)

pAtom :: Parser Raw
pAtom =
  withPos (pVar <|> (RU <$ symbol "U") <|> (RTiny <$ symbol "T") <|> (RTiny0 <$ symbol "0") <|> (RTiny1 <$ symbol "1"))
    <|> parens pRaw

pBinder :: Parser Name
pBinder = pIdent <|> symbol "_"

pSpine :: Parser Raw
pSpine = foldl1 RApp <$> some pAtom

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

pRaw :: Parser Raw
pRaw =
  withPos
    ( pLam
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

pSrc :: Parser Raw
pSrc = ws *> pRaw <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t ->
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  file <- getContents
  tm <- parseString file
  pure (tm, "(stdin)")

parseFile :: String -> IO (Raw, String)
parseFile fn = do
  file <- readFile fn
  tm <- parseString file
  pure (tm, file)
