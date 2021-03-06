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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Core.Expression where

-- import Prelude hiding (lookup)
-- import Data.Foldable
-- import Test.QuickCheck
--import Data.String
--import qualified Data.Map as Map
--import Data.Map (Map)
--import Data.String (IsString(..))
--import Data.Kind (Type)

-- Core
import Core.Parser.SrcLoc
import Core.Quantity


type Name  = String
type DBInd = Int
type DBLvl = Int
type MetaVar = Int

newVar :: Name
newVar = "x"

dummyBindInfo :: BindInfo
dummyBindInfo =
  BindInfo
    { bind_name     = "_"
    , bind_quantity = Inf
    }


metaBindInfo :: BindInfo
metaBindInfo =
  BindInfo
  { bind_name     = "?meta"
  , bind_quantity = Inf
  }

type Chars = String

data PrimBinOp where
  PAddI :: PrimBinOp
  deriving (Eq, Ord, Show)

data PrimTy where
  PTyInt :: PrimTy
  deriving (Eq, Ord, Show)

data Prim  where
  PInt :: Int -> Prim
  deriving (Eq, Ord, Show)

data BindInfo = BindInfo
  { bind_name     :: Name
  , bind_quantity :: Quantity
  }
  deriving (Eq, Ord, Show)

-- TO DO: add type synonym / newtype for RawExpr which are to be interpretted as types
-- and use in places where it would be appropriate. Do the same also for Expr
-- e.g.
-- LetR Name RawExpr RawExpr RawExpr
-- should really look something like

--   LetR Name RawType RawBind RawExpr
--
-- One idea is to follow McBride and add a Bind newtype so we have:
--
-- newtype Bind e = Bind {unBind :: e}
--
-- type RawBind = Bind RawExpr
--
-- Unclear if this alone would just be annoying but worth an experiment.

-- The Raw AST which we feed to elaboration
data RawExpr =
    LocR Name                                                -- local variable
  | TopR String                                              -- top level name
  | PiR BindInfo RawExpr RawExpr                            -- (q a : A) -> B
  | LamR Name RawExpr                                        -- fun x => expr
  | AppR RawExpr RawExpr                                     -- rator rand
  | SigmaR BindInfo RawExpr RawExpr                              -- ((q a : A) * B)
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
  | PrimR Prim                                               -- primitive data
  | PrimTyR PrimTy                                           -- primitive types
  | PrimBinOpR PrimBinOp RawExpr RawExpr                     -- primitive ops
  | LetR BindInfo RawExpr RawExpr RawExpr                        -- let x : A = v; body
  | SrcPosR SrcPos RawExpr                                   -- expr with src pos
  | MetaR Name                                               -- ?

  deriving (Eq, Ord, Show)


data CoreDef = CoreDef
  { coreDef_name :: Name 
  , coreDef_Expr :: Expr
  }
  deriving (Eq, Ord, Show)


-- Core AST after renaming and elaboration.
data Expr =
    Loc DBInd                             -- local variable
  | Top Name                              -- top level name
  | Pi BindInfo Expr Expr                 -- (q a : A) -> B
  | Lam Name Expr                         -- fun x => expr
  | Let Name Expr Expr Expr                    -- let x : A = v; body
  | App Expr Expr                         -- rator rand
  | Sigma BindInfo Expr Expr              -- ((q a : A) * B)
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
  | Prim Prim                             -- primitive data
  | PrimTy PrimTy                         -- primitive types
  | PrimBinOp PrimBinOp Expr Expr         -- primitive ops
  | Meta MetaVar
  | InsertedMeta MetaVar [Bool]
  deriving (Eq, Ord, Show)

pattern Var :: Int -> Expr
pattern Var n <- Loc n
  where
    Var v = Var v

--pattern Arr :: Expr -> Expr -> Expr
--pattern Arr e1 e2 = Pi "_" e1 e2
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
