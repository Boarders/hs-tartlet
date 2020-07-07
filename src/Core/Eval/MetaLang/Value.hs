{-# LANGUAGE Strict          #-}
{-# LANGUAGE RecordWildCards #-}

module Core.Eval.MetaLang.Value where


import Core.Expression
import Control.Monad
import Control.Applicative
import Data.String

type TopEnv   = [(Name, Normal)]

type LocalEnv = [Value]
type Ctx = (TopEnv, LocalEnv)

extendEnv :: LocalEnv -> Value -> LocalEnv
extendEnv env val = (val : env)


type Ty = Value

data Value =
    VPi Name Ty (Value -> Value)
  | VLam Name (Value -> Value)
  | VSigma Name Ty (Value -> Value)
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
  | NVar Int
  | NApp Neutral Normal
  | NCar Neutral
  | NCdr Neutral
  | NIndNat Neutral Normal Normal Normal
  | NReplace Neutral Normal Normal
  | NIndAbsurd Neutral Normal


data Normal = Normal
  { normalTy  :: Ty
  , normalVal :: Value
  }
