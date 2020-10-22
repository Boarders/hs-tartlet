{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies   #-}

module Core.Expression where

-- import Prelude hiding (lookup)
-- import Data.Foldable
-- import Test.QuickCheck
--import Data.String
import qualified Data.Map as Map
import Data.Map (Map)
import Data.String (IsString(..))


type Name  = String
type DBInd = Int
type DBLvl = Int
type MetaVar = Int

newVar :: Name
newVar = "x"

dummyVar :: Name
dummyVar ="_"

metaVar :: Name
metaVar = "?meta"

type Chars = String

-- The Raw AST which we feed to elaboration
data RawExpr =
    LocR Name                                                -- local variable
  | TopR String                                              -- top level name
  | PiR Name RawExpr RawExpr                                 -- (a : A) -> B
  | LamR Name RawExpr                                        -- fun x => expr
  | AppR RawExpr RawExpr                                     -- rator rand
  | SigmaR Name RawExpr RawExpr                              -- ((a : A) * B)
  | ConsR RawExpr RawExpr                                    -- cons fst snd
  | CarR RawExpr                                             -- car p
  | CdrR RawExpr                                             -- cdr p
  | NatR                                                     -- Nat
  | ZeroR                                                    -- zero
  | Add1R RawExpr                                            -- add1
  | IndNatR RawExpr RawExpr RawExpr RawExpr                  -- ind-Nat tgt mot base step
  | EqualR RawExpr RawExpr RawExpr                           -- Eq A from to
  | SameR                                                    -- Refl
  | ReplaceR RawExpr RawExpr RawExpr                         -- trans
                                                               --   (eq : eq P from to)
                                                               --   (mot : P -> Type)
                                                               --   base : mot from
  | UnitR                                                    -- Unit
  | SoleR                                                    -- tt : Unit
  | AbsurdR                                                  -- Absurd
  | IndAbsurdR RawExpr RawExpr                               -- ind-Absurd (tgt : False) (ty : Type)
  | AtomR                                                    -- Atom
  | TickR Chars                                              -- 'a
  | UnivR                                                    -- Type
  | TheR RawExpr RawExpr                                     -- (exp : ty)
  | HoleR                                                    -- _
  deriving (Eq, Ord, Show)


-- Core AST after renaming and elaboration.
data Expr =
    Loc DBInd                               -- local variable
  | Top Name                              -- top level name
  | Pi Name Expr Expr                     -- (a : A) -> B
  | Lam Name Expr                         -- fun x => expr
  | App Expr Expr                         -- rator rand
  | Sigma Name Expr Expr                  -- ((a : A) * B)
  | Cons Expr Expr                        -- cons fst snd
  | Car Expr                              -- car p
  | Cdr Expr                              -- cdr p
  | Nat                                   -- Nat
  | Zero                                  -- zero
  | Add1 Expr                             -- add1
  | IndNat Expr Expr Expr Expr            -- ind-Nat tgt mot base step
  | Equal Expr Expr Expr                  -- Eq A from to
  | Same                                  -- Refl
  | Replace Expr Expr Expr                -- trans
                                          --   (eq : eq P from to)
                                          --   (mot : P -> Type)
                                          --   base : mot from
  | Trivial                               -- Unit
  | Sole                                  -- tt : Unit
  | Absurd                                -- Absurd
  | IndAbsurd (Expr) (Expr)               -- ind-Absurd (tgt : False) (ty : Type)
  | Atom                                  -- Atom
  | Tick Chars                            -- 'a
  | U                                     -- Type
  | The Expr Expr                         -- (exp : ty)
  | Meta MetaVar --to do : [Sp]               -- ?n
  | InsertedMeta MetaVar [Bool]               -- ?n bd_1 ... bd_d
  deriving (Eq, Ord, Show)

pattern Var :: Int -> Expr
pattern Var n <- Loc n
  where
    Var v = Var v

{-
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



-}
