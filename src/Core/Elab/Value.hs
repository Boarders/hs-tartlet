{-# LANGUAGE Strict          #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}

module Core.Elab.Value where

import Core.Expression

type TopEnv   = [(Name, Normal)]
type LocalEnv = [Value]
type TyEnv = [Ty]
type Ctxt = (TopEnv, LocalEnv)
type VEnv = [Value]
  --Env Value

extendEnv :: LocalEnv -> Value -> LocalEnv
extendEnv env val = (val : env)

extendTyEnv :: TyEnv -> Ty -> TyEnv
extendTyEnv tyEnv ty = (ty : tyEnv)


data Closure = Closure VEnv Expr

constClos :: Expr -> Closure
constClos expr = Closure mempty expr

data VCl = VCl VEnv RawExpr
--data GCl = GCl GEnv VEnv RawExpr



type Ty = Value
type Meta = Int

data Value =
    VPi Name Ty Closure
  | VLam Name Closure
  | VSigma Name Ty Closure
  | VPair Value Value
  | VNat
  | VZero
  | VAdd1 Value
  | VEqual Ty Value Value
  | VSame
  | VTrivial
  | VSole
  | VAbsurd
  | VAtom
  | VTick Chars
  | VU
  | VTop Name Neutral ~(Maybe Ty) ~Value
  | VNeutral (Maybe Ty) Neutral
  | VPrim Prim
  | VPrimTy PrimTy



cmpConstrs :: Value -> Value -> Bool
cmpConstrs lhs rhs = case (lhs, rhs) of
  (VNat, VNat) -> True
  (VZero, VZero) -> True
  (VSame, VSame) -> True
  (VTrivial, VTrivial) -> True
  (VSole, VSole) -> True
  (VAbsurd, VAbsurd) -> True
  (VAtom, VAtom) -> True
  (VTick cs1, VTick cs2) -> cs1 == cs2
  (VU, VU) -> True
  (VPrim p1, VPrim p2) -> p1 == p2
  (_,_) -> False


data Head = HMeta Meta | HVar Int | HTop Name
  deriving (Eq)

data Neutral =
    NSpine Head [Normal]
  | NCar Neutral
  | NCdr Neutral
  | NIndNat Neutral Normal Normal Normal
  | NReplace Neutral Normal Normal
  | NIndAbsurd Neutral Normal
  | NPrimBinOp PrimBinOp Neutral Normal


pattern NTop :: Name -> Neutral
pattern NTop n = NSpine (HTop n) []

pattern NVar :: Int -> Neutral
pattern NVar n = NSpine (HVar n) []

pattern VVarT :: Ty -> Int -> Value
pattern VVarT ty n = VNeutral (Just ty) (NSpine (HVar n) [])

pattern VVar :: Int -> Value
pattern VVar n = VNeutral Nothing (NSpine (HVar n) [])

pattern VMeta :: Int -> Value
pattern VMeta n = VNeutral Nothing (NSpine (HMeta n) [])

pattern VMetaSp :: Int -> [Normal] -> Value
pattern VMetaSp m sp = VNeutral Nothing (NSpine (HMeta m) sp)

data Normal = Normal
  { normalTy  :: Maybe Ty
  , normalVal :: Value
  }
