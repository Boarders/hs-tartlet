{
module Token where
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
  =>          { \s -> MapsTo }
  *           { \s -> Star }
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
  False        { \s -> False }
  
  


  $digit+				{ \s -> Int (read s) }
  [\=\+\-\*\/\(\)]			{ \s -> Sym (head s) }
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
  False         |
  IndAbsurd     |
  Atom          |
  Tick String   |
  Sym Char      |
  Univ
  deriving (Eq,Show)

token = alexScanTokens
}
