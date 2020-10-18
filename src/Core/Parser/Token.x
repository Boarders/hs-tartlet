
  {
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module Core.Parser.Token where

import qualified Data.ByteString.Lazy.Char8 as Char8
import qualified Data.ByteString.Lazy as ByteString
}

%wrapper "monad-bytestring"

$digit = 0-9        -- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-
  $white+    ;
  "--".*     ;
  \(          { tok LeftBracket  }
  \)          { tok RightBracket }
  :           { tok Ann }
  \->         { tok Arr }
  fun         { tok Fun }
  =>          { tok MapsTo }
  \*          { tok Star }
  cons        { tok Cons }
  car         { tok Car  }
  cdr         { tok Cdr  }
  \Nat | ℕ    { tok Nat  }
  0 | zero    { tok Zero }
  succ | add1 { tok Add1 }
  ind\-Nat    { tok IndNat }
  Eq          { tok  Eq }
  refl        { tok  Refl }
  Unit        { tok  Unit }
  \(\) | tt   { tok  TT   }
  Absurd      { tok Absurd }
  ind\-Absurd { tok IndAbsurd }
  atom        { tok Atom }
  \' [$alpha $digit]* { tok_app Tick}
  $alpha [$alpha $digit \_ \']*		{ tok_app Var }


{
-- Each action has type :: String -> Token
tok'
  :: (ByteString.ByteString -> TokenType)
  -> (AlexPosn, a, ByteString.ByteString, b)
  -> Int64
  -> Alex Token
tok' f (pos, _, input, _) len = return $ Token pos (f (Char8.take (fromIntegral len) input))
tok :: TokenType -> (AlexPosn, a, ByteString.ByteString, b) -> Int64 -> Alex Token
tok x = tok' (\s -> x)
tok_app :: (String -> TokenType) -> (AlexPosn, a, ByteString.ByteString, b) -> Int64 -> Alex Token
tok_app f = tok' (\s -> f (Char8.unpack s))


type Chars = String

data Token = Token AlexPosn TokenType
  deriving (Eq, Show)

-- The token type:
data TokenType =
  LeftBracket   |
  RightBracket  |  
  Var Chars     |
  Ann           |
  Arr           |
  Fun           |
  MapsTo        |
  Star          |
  Cons          |
  Car           |
  Cdr           |
  Nat           |
  Zero          |
  Add1          |
  IndNat        |
  Eq            |
  Refl          |
  Trans         |
  Unit          |
  TT            |
  Absurd        |
  IndAbsurd     |
  Atom          |
  Tick String   |
  Univ          |
  EOF
  deriving (Eq,Show)


alexEOF :: Alex Token
alexEOF = do
  (pos, _, _, _) <- alexGetInput
  return $ Token pos EOF

scanToken :: ByteString.ByteString -> Either String Token
scanToken str = runAlex str alexMonadScan


scanTokenM :: (Token -> Alex a) -> Alex a
scanTokenM = (alexMonadScan >>=)
}
