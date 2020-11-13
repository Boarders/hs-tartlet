{-# language OverloadedStrings #-}
module Main where

import System.Console.Haskeline
import Data.Foldable
import System.Console.ANSI
import Control.Monad.IO.Class


import Data.Text (Text, unpack)
import Data.Void
import Data.String (fromString)

-- import Core.PrettyPrint
import Core.Expression
import qualified Text.Parsec as Parsec
import Core.Pretty.Error
import Prettyprinter
import qualified Data.Text as Text
import Data.Text (Text)
import Core.Parser.SrcLoc as Loc
import Data.Text.Prettyprint.Doc.Render.Terminal

err :: Text
err = Text.unlines
  [ "This is the first line."
  ,"     error here"
  ]

errSrcPos :: SrcPos
errSrcPos = Loc.SrcPos 0 2 6


errMsg = "It's an error!"

main :: IO ()
main =
  let
    errorDoc = printTextError 80 err errSrcPos errMsg "Your error type"
    ansiDoc  = reAnnotate toAnsiAttr errorDoc
  in
    putDoc ansiDoc
  
{-  
  -- runInputT settings repl
   where
     repl :: InputT IO ()
     repl = header >> mainLoop

     header :: InputT IO ()
     header = do
       outputStrLn ""
       headerImage
       quitInfo


     mainLoop :: InputT IO ()
     mainLoop = do
       minput <- getInputLine "λ  "
       case minput of
         Nothing -> return ()
         Just ":quit" -> return ()
         Just ":q"    -> return ()
         Just input ->
           case lexInput input of
             Left err -> do
               outputStrLn "Lex error: "
               outputStrLn (show err)
               mainLoop
             Right expr -> do
               outputStrLn "Lex: "
               outputStrLn (show (fmap fst expr))
               outputStrLn ""
               case typeInput expr of
                 Left err -> do
                   outputStrLn "Parse error: "
                   outputStrLn (show err)
                   mainLoop
                 Right ty -> do
                   outputStrLn "Parse: "
                   outputStrLn (show ty)
                   mainLoop

type Token = (Int, Int)
type Type a = [a]

lexInput :: String -> Either Parsec.ParseError [Token]
lexInput = undefined -- Parsec.runParser lexTerm () ""

typeInput :: [Token] -> Either Parsec.ParseError (Type String)
typeInput = undefined -- Parsec.runParser parseType () ""


settings :: MonadIO m => Settings m
settings = Settings
  { complete       = completeFilename
  , historyFile    = Just ".bidirection"
  , autoAddHistory = True
  }

{-
outputWithSpace :: String -> InputT IO ()
outputWithSpace str =
  do
    outputStrLn $ mempty
    outputStrLn $ str
    outputStrLn $ mempty

expressionOutput :: Term String -> InputT IO ()
expressionOutput e
  = traverse_ outputWithSpace (outputContent e)

outputContent :: Term String -> [String]
outputContent e =
  [ "Lambda Term String is: "
  , unpack $ printExpr 0 e
  , "The Tree representation is: "
  , printAsTree e
  , "The SKI term is: "
  , printSKI (toSKIRep e)
  ]
-}

headerImage :: InputT IO ()
headerImage =
  do
    liftIO $ setSGR [SetColor Foreground Vivid Blue]
    liftIO $ putStrLn headerText
    liftIO $ setSGR [Reset]  -- Reset to default colour scheme
    liftIO $ putStrLn ""


headerText :: String
headerText = unlines
  [" ####   ##  #####   ##  #####   ####   ####  ######  ##    ###    ##    ##   ####   ##   "
  ," ## ##  ##  ##  ##  ##  ##  ##  ##    ##       ##    ##  ##   ##  ###   ##  ##  ##  ##   "
  ," ####   ##  ##  ##  ##  #####   ###   ##       ##    ##  ##   ##  ## ## ##  ######  ##   "
  ," ## ##  ##  ##  ##  ##  ## ##   ##    ##       ##    ##  ##   ##  ##   ###  ##  ##  ##   "
  ," ####   ##  #####   ##  ##  ##  ####   ####    ##    ##    ###    ##    ##  ##  ##  #####"
  ]


welcomeMessage :: InputT IO ()
welcomeMessage =
  do
    liftIO $ setSGR [SetColor Foreground Vivid Green]
    liftIO $ putStrLn (replicate 30 ' ' <> "Welcome friend!")
    liftIO $ setSGR [Reset]  -- Reset to default colour scheme
    liftIO $ putStrLn ""


quitInfo :: InputT IO ()
quitInfo =
  do
    liftIO $ setSGR [SetColor Foreground Vivid Green]
    liftIO $ putStrLn "Type :quit or :q to exit!"
    liftIO $ setSGR [Reset]  -- Reset to default colour scheme
    liftIO $ putStrLn ""
-}
