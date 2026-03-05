module Main where

import Control.Monad (forM_)
import System.Environment (getArgs)
import Text.Megaparsec (SourcePos (SourcePos), initialPos, unPos)
import Text.Printf (printf)

import Tiny.Check (withEmptyCtx, withGlobals, inferProgram)
import Tiny.Core (nf, quote)
import Tiny.Parser (parseFile, parseStdin, parseString)
import Tiny.Pretty ()
import Tiny.Syntax (RawProgram)
import Tiny.Value

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

mainWith :: IO [String] -> IO (RawProgram, String) -> IO ()
mainWith getOpt getRaw = do
  opts <- getOpt
  case opts of
    ["nf"] -> do
      (t, file) <- getRaw
      case withEmptyCtx (initialPos file) (inferProgram t) of
        Left err -> displayError file err
        Right (gs, Nothing) -> putStrLn "Checked!"
        Right (gs, Just (t, ty)) -> do
          let nft = withEmptyCtx (initialPos file) $ withGlobals gs $ nf t
          print nft
          putStrLn "  :"
          print ty
    ["type"] -> do
      (t, file) <- getRaw
      case withEmptyCtx (initialPos file) (inferProgram t) of
        Left err -> displayError file err
        Right (Globals _, Nothing) -> putStrLn "Checked!"
        Right (Globals _, Just (_, ty)) -> print ty
    ["types"] -> do
      (t, file) <- getRaw
      case withEmptyCtx (initialPos file) (inferProgram t) of
        Left err -> displayError file err
        Right (Globals gs, _) -> forM_ (reverse gs) $ \(x, (v, vty)) ->
          let ty = withEmptyCtx (initialPos file) $ withGlobals (Globals gs) $ quote vty in
          putStrLn (x ++ " : " ++ show ty)
    _ -> putStrLn "unknown option"

main :: IO ()
main = mainWith getArgs parseStdin

main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((\tm -> (tm, src)) <$> parseString src)

mainFile :: String -> String -> IO ()
mainFile mode fn = mainWith (pure [mode]) (parseFile fn)
