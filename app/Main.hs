module Main where

import System.Environment (getArgs)
import Text.Megaparsec (SourcePos (SourcePos), initialPos, unPos)
import Text.Printf (printf)

import Tiny.Check (infer, withEmptyCtx)
import Tiny.Core (nf, quote)
import Tiny.Parser (parseFile, parseStdin, parseString)
import Tiny.Pretty ()
import Tiny.Syntax (Raw)

displayError :: String -> (String, SourcePos) -> IO ()
displayError file (msg, pos) = do
  let SourcePos path l c = pos
      linum = unPos l
      colnum = unPos c
      lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n" lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do
  opts <- getOpt
  case opts of
    ["nf"] -> do
      (t, file) <- getRaw
      case withEmptyCtx (initialPos file) (infer t) of
        Left err -> displayError file err
        Right (t', a) -> do
          print $ withEmptyCtx (initialPos file) (nf t')
          putStrLn "  :"
          print $ withEmptyCtx (initialPos file) (quote a)
    ["type"] -> do
      (t, file) <- getRaw
      case withEmptyCtx (initialPos file) (infer t) of
        Left err -> displayError file err
        Right (_, a) -> print $ withEmptyCtx (initialPos file) (quote a)
    _ -> putStrLn "unknown option"

main :: IO ()
main = mainWith getArgs parseStdin

main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((\tm -> (tm, src)) <$> parseString src)

mainFile :: String -> String -> IO ()
mainFile mode fn = mainWith (pure [mode]) (parseFile fn)
