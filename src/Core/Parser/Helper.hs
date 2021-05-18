
module Core.Parser.Helper
  ( thenP
  , returnP
  , happyError
  , Parser
  , AlexPosn
  , AlexState(..)
  , lexer
  , runAlex
  , runParser
  )
  where

----------------------------------------------------------------------------
-- Core
import Core.Parser.Token

-- bytestring
import Data.ByteString.Lazy as ByteString
----------------------------------------------------------------------------

-- For readablity - these are the interfaces Happy expects:

type Parser a = Alex a

thenP :: Parser a -> (a -> Parser b) -> Parser b
thenP = (>>=)

runParser :: Parser a -> ByteString -> Either String a
runParser p s = runAlex s p

returnP :: a -> Parser a
returnP = return

alexShowError :: (Show t, Show t1) => (t, t1, Maybe String) -> Alex a
alexShowError (line, column, e) = alexError $ "show-error: " ++ (show (line, column, e))

alexGetPosition :: Alex (AlexPosn)
alexGetPosition = Alex $ \s@AlexState{alex_pos=pos} -> Right (s, pos)

happyError :: Parser a
happyError = do
  (AlexPn _ line col) <- alexGetPosition
  alexShowError (line, col, Nothing)

lexer :: (Token -> Parser a) -> Parser a
lexer = scanTokenM
