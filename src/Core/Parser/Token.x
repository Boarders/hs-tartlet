{
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module Core.Parser.Token where
}

%wrapper "basic"

$digit = 0-9      -- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-
  $white+    ;
  "--".*     ;
  \(          { \s -> LeftBracket  }
  \)          { \s -> RightBracket }
  :           { \s -> Ann }
  \->         { \s -> Arr }
  fun         { \s -> Fun }
  =>          { \s -> MapsTo }
  \*          { \s -> Star }
  cons        { \s -> Cons }
  cdr         { \s -> Cdr  }
  \Nat | ℕ    { \s -> Nat  }
  0 | zero    { \s -> Zero }
  succ | add1 { \s -> Add1 }
  ind\-Nat     { \s -> IndNat }
  Eq           { \s -> Eq }
  refl         { \s -> Refl }
  Unit         { \s -> Unit }
  \(\) | tt    { \s -> TT   }
  Absurd        { \s -> Absurd }
  ind\-Absurd  { \s -> IndAbsurd }
  atom         { \s -> Atom }
  \' [$alpha $digit]* { \s -> Tick s}
  $alpha [$alpha $digit \_ \']*		{ \s -> Var s }


{
-- Each action has type :: String -> Token

type Chars = String

-- The token type:
data Token =
  LeftBracket   |
  RightBracket  |  
  Var Chars     |
  Ann           |
  Arr           |
  Fun           |
  MapsTo        |
  Star          |
  Cons          |
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
  Univ
  deriving (Eq,Show)

scanToken :: String -> [Token]
scanToken = alexScanTokens
}
