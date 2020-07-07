module Core.Eval.EnvMachine.Value where

import Core.Expression

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
getClosureName = closureName


type Ty = Value

data Value =
    VPi Ty Closure
  | VLam Closure
  | VSigma Ty Closure
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
