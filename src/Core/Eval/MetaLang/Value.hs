{-# LANGUAGE Strict          #-}
{-# LANGUAGE RecordWildCards #-}

module Core.Eval.MetaLang.Value where


import Core.Expression
import Control.Monad
import Control.Applicative
import Data.String

type TopEnv = [(Name, Normal)]
type LocalEnv = [(Name, Maybe Value)]

extendEnv :: LocalEnv -> Name -> Value -> LocalEnv
extendEnv env v val = ((v, Just val) : env)


findMaxId :: LocalEnv -> String -> Maybe Int
findMaxId ctx str = go Nothing ctx
  where
    go acc [] = acc
    go acc ((Name{..}, _) : xs) | str == name = go (liftA2 max acc (Just iD)) xs
                                | otherwise = go acc xs
             
freshen :: LocalEnv -> String -> Name
freshen ctx str =
  case findMaxId ctx str  of
    Nothing -> fromString str
    Just k  -> Name (k + 1) str



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

