{-# LANGUAGE Strict #-}

module Core.Eval.MetaLang.Value where


import Core.Expression
import Control.Monad

type TopEnv = [(Name, Normal)]
type LocalEnv = [(Name, Maybe Value)]

extendEnv :: LocalEnv -> Name -> Value -> LocalEnv
extendEnv env v val = ((v, Just val) : env)




type Ty = Value

data Value =
    VPi Ty (Value -> Value)
  | VLam Name (Value -> Value)
  | VSigma Ty (Value -> Value)
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
  | VTop Name Neutral ~Ty ~Value
  | VNeutral Ty Neutral


data Neutral =
    NTop Name
  | NVar Name
  | NApp Neutral Normal
  | NCar Neutral
  | NCdr Neutral
  | NIndNat Neutral Normal Normal Normal
  | NReplace Neutral Normal Normal
  | NIndAbsurd Neutral Normal


data Normal = Normal
  { normalTy   :: Ty
  , normalVal :: Value
  }

