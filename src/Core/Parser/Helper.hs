
module Core.Parser.Helper
  ( thenP
  , returnP
  , happyError
  , Parser
  , Token(..)
  , tokenToPosN
  , TokenClass(..)
  , AlexPosn
  , AlexState(..)
  , lexer
  , runAlex
  )
  where

----------------------------------------------------------------------------
import Core.Parser.Token
----------------------------------------------------------------------------

-- For readablity - these are the interfaces Happy expects:

type Parser a = Alex a

thenP :: Parser a -> (a -> Parser b) -> Parser b
thenP = (>>=)

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