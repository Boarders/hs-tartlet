{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}

module Core.Expression where

-- import Prelude hiding (lookup)
-- import Data.Foldable
-- import Test.QuickCheck
--import Data.String
import qualified Data.Map as Map
import Data.Map (Map)
import Data.String (IsString(..))


data Name = Name
  { iD :: !Int
  , name :: String
  }
  deriving (Eq, Ord)

instance Show Name where
  show (Name 0 str) = str
  show (Name n str) = str <> (show n)

instance IsString Name where
  fromString str = Name 0 str

newVar :: Name
newVar = "x"

type Chars = String

data Expr =
    Var Name                              -- v
  | Pi Name (Expr) (Expr)                 -- (a : A) -> B
  | Lam Name (Expr)                       -- fun x => expr
  | App (Expr) (Expr)                     -- rator rand
  | Sigma Name (Expr) (Expr)              -- (a : A) x B
  | Cons (Expr) (Expr)                    -- cons fst snd
  | Car (Expr)                            -- car p
  | Cdr (Expr)                            -- cdr p
  | Nat                                   -- nat
  | Zero                                  -- zero
  | Add1 (Expr)                           -- add1
  | IndNat (Expr) (Expr) (Expr) (Expr)    -- ind-Nat tgt mot base step
  | Equal (Expr) (Expr) (Expr)            -- eq A from to
  | Same                                  -- refl
  | Replace (Expr) (Expr) (Expr)          -- trans
                                          --   (eq : eq P from to)
                                          --   (mot : P -> Type)
                                          --   base : mot from
  | Trivial                               -- Unit
  | Sole                                  -- t : Unit
  | Absurd                                -- False
  | IndAbsurd (Expr) (Expr)               -- ind-Absurd (tgt : False) (ty : Type)
  | Atom                                  -- Atom
  | Tick Chars                            -- 'a
  | U                                     -- Type
  | The (Expr) (Expr)                     -- (exp : ty)
  deriving (Eq, Ord, Show)


newtype Env = Env [(Name, Value)]
  deriving (Eq, Ord, Show)

extendEnv :: Env -> Name -> Value -> Env
extendEnv (Env env) v val = Env ((v, val) : env)

evalVar :: Env -> Name -> Value
evalVar (Env []) v = error $ "evalVar: Unable to find variable " <> (show v)
evalVar (Env ((y, val) : env)) x
  | x == y = val
  | otherwise = evalVar (Env env) x

emptyEnv :: Env
emptyEnv = Env []
                                   
  

data Closure = Closure
  { closureEnv  :: Env
  , closureName :: Name
  , closureBody :: Expr
  }
  deriving (Eq, Ord, Show)

getClosureName :: Closure -> String
getClosureName = name . closureName


type Ty = Value

data Value =
    VPi Ty Closure
  | VLam Closure
  | VSigma Ty Closure
  | VPair Value Value
  | VNat
  | VZero
  | VAdd1 Value
  | VEq Ty Value Value
  | VSame
  | VTrivial
  | VSole
  | VAbsurd
  | VAtom
  | VTick Chars
  | VU
  | VNeutral Ty Neutral
  deriving (Eq, Ord, Show)


data Neutral =
    NVar Name
  | NApp Neutral Normal
  | NCar Neutral
  | NCdr Neutral
  | NIndNat Neutral Normal Normal Normal
  | NReplace Neutral Normal Normal
  | NIndAbsurd Neutral Normal
  deriving (Eq, Ord, Show)


data Normal = Normal Ty Value
  deriving (Eq, Ord, Show)



alphaEquiv :: Expr -> Expr -> Bool
alphaEquiv e1 e2 = alphaHelper 0 (Map.empty) e1 (Map.empty) e2
  where
-- To do: write custom expression traversal for bound and unbound
-- variables and then use this to re-write this in a slicker way
  alphaHelper :: Int -> Map Name Int -> Expr -> Map Name Int -> Expr -> Bool
  alphaHelper b ns1 (Var x) ns2 (Var y) =
    case (Map.lookup x ns1, Map.lookup y ns2) of
      (Nothing, Nothing) -> x == y
      (Just i, Just j)   -> i == j
      _                  -> False

  alphaHelper b ns1 (Lam x body1) ns2 (Lam y body2) =
    alphaHelper (b + 1) (Map.insert x b ns1) body1 (Map.insert y b ns2) body2

  alphaHelper b ns1 (App rat1 rand1) ns2 (App rat2 rand2) =
    alphaHelper b ns1 rat1 ns2 rat2 &&
    alphaHelper b ns1 rand1 ns2 rand2

  alphaHelper b ns1 (Sigma x dom1 ran1) ns2 (Sigma y dom2 ran2) =
    alphaHelper b ns1 dom1 ns2 dom2 &&
    alphaHelper (b + 1) (Map.insert x b ns1) ran1 (Map.insert y b ns2) ran2

  alphaHelper b ns1 (Cons f1 s1) ns2 (Cons f2 s2) =
    alphaHelper b ns1 f1 ns2 f2 && alphaHelper b ns1 f1 ns2 f2

  alphaHelper b ns1 (Car p1) ns2 (Car p2) =
    alphaHelper b ns1 p1 ns2 p2

  alphaHelper b ns1 (Cdr p1) ns2 (Cdr p2) =
    alphaHelper b ns1 p1 ns2 p2

  alphaHelper b ns1 (Add1 e1) ns2 (Add1 e2) =
    alphaHelper b ns1 e1 ns2 e2

  alphaHelper b ns1 (IndNat tgt1 mot1 base1 step1) ns2 (IndNat tgt2 mot2 base2 step2) =
    alphaHelper b ns1 tgt1 ns2 tgt2   &&
    alphaHelper b ns1 mot1 ns2 mot2   &&
    alphaHelper b ns1 base1 ns2 base2 &&
    alphaHelper b ns1 step1 ns2 step2

  alphaHelper b ns1 (Equal ty1 from1 to1) ns2 (Equal ty2 from2 to2) =
    alphaHelper b ns1 ty1 ns2 ty2     &&
    alphaHelper b ns1 from1 ns2 from2 &&
    alphaHelper b ns1 to1   ns2 from2

  alphaHelper b ns1 (Replace eq1 mot1 base1) ns2 (Replace eq2 mot2 base2) =
    alphaHelper b ns1 eq1 ns2 eq2   &&
    alphaHelper b ns1 mot1 ns2 mot2 &&
    alphaHelper b ns1 base1 ns2 base2

  alphaHelper b ns1 (IndAbsurd tgt1 ty1) ns2 (IndAbsurd tgt2 ty2) =
    alphaHelper b ns1 tgt1 ns2 tgt2 &&
    alphaHelper b ns1 ty1  ns1 ty2

  alphaHelper b ns1 (The e1 ty1) ns2 (The e2 ty2) =
    alphaHelper b ns1 e1 ns2 e2 &&
    alphaHelper b ns1 ty1 ns2 ty2

-- if both values are of type absurd then skip alpha equivalence test
  alphaHelper _ _ (The Absurd _) _ (The Absurd _) = True
  alphaHelper _ _ term1 _ term2 = term1 == term2

  

  
  
  
