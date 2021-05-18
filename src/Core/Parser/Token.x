
  {
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module Core.Parser.Token where

import qualified Core.Quantity as Quantity
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
  Nat | ℕ     { tok Nat  }
  zero        { tok NatZero }
  0           { tok Zero }
  1           { tok One  }
  W           { tok Inf  }
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

data Token = Token
  { getPos   :: AlexPosn
  , getToken :: TokenType
  }
  deriving (Eq, Show)

-- The token type:
data TokenType =
  LeftBracket   |
  RightBracket  |  
  Int Int       |
  Var String    |
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
  One           |
  Inf           |
  NatZero       |
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


getTick :: Token -> Chars
getTick = unTick . getToken

getVar :: Token -> Chars
getVar = unVar . getToken

unVar :: TokenType -> Chars
unVar (Var c) = c
unVar _ = error "Token.x.unVar: used on argument without Var"

unTick :: TokenType -> Chars
unTick (Tick c) = c
unTick _ = error "Token.x.unTick: used on argument without Tick"


getQuantity :: Token -> Quantity.Quantity
getQuantity = toQuantity . getToken

toQuantity :: TokenType -> Quantity.Quantity
toQuantity Zero = Quantity.Zero
toQuantity One  = Quantity.One
toQuantity Inf  = Quantity.Inf
toQuantity _    = error "Token.x.toQuantity: used on non-quantity argument"

alexEOF :: Alex Token
alexEOF = do
  (pos, _, _, _) <- alexGetInput
  return $ Token pos EOF

scanToken :: ByteString.ByteString -> Either String Token
scanToken str = runAlex str alexMonadScan


scanTokenM :: (Token -> Alex a) -> Alex a
scanTokenM = (alexMonadScan >>=)
}
