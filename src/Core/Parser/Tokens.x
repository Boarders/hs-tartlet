{
module Token where
}

%wrapper "basic"

$digit = 0-9			  -- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-

  $white+				;
  "--".*				;
  :					{ \s -> Let }
  in			  { \s -> In }
  $digit+				{ \s -> Int (read s) }
  [\=\+\-\*\/\(\)]			{ \s -> Sym (head s) }
  $alpha [$alpha $digit \_ \']*		{ \s -> Var s }

{
-- Each action has type :: String -> Token

type Chars = String

-- The token type:
data Token =
	Var Chars 		|
	Ann       		|
  MapsTo        |
  Prod          |
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
	Sym Char	    |
	Univ
	deriving (Eq,Show)

token = alexScanTokens
}
