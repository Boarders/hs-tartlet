{-# LANGUAGE OverloadedStrings #-}
module Core.Eval where

import Core.Expression
import Core.Context


eval :: Env -> Expr -> Value
eval = undefined

evalClosure :: Closure -> Value -> Value
evalClosure (Closure env var body) val = eval (extendEnv env var val) body

doCar :: Value -> Value
doCar (VPair f _) = f
doCar (VNeutral (VSigma domT _) neu) = VNeutral domT (NCar neu)
doCar val = tyCheckError "doCar" [val]

doCdr :: Value -> Value
doCdr (VPair _ s) = s
doCdr neuV@(VNeutral (VSigma _ depT) neu) =
  let
    subDepT = evalClosure depT (doCar neuV)
  in
    VNeutral subDepT (NCdr neu)
doCdr val = tyCheckError "doCdr" [val]


doApply :: Value -> Value -> Value
doApply (VLam (Closure env var body)) arg =
  eval (extendEnv env var arg) body
doApply (VNeutral (VPi domT depT) neu) arg =
  let
    subDepT = evalClosure depT arg
  in
    VNeutral subDepT (NApp neu (Normal domT arg))
doApply fun arg = tyCheckError "doApply" [fun, arg]

doReplace :: Value -> Value -> Value -> Value
doReplace VSame _ base = base
doReplace (VNeutral (VEq ty from to) neu) mot base =
  let
    transTgt = doApply mot to
    motT     = VPi ty (Closure emptyEnv newVar U)
    baseT    = doApply motT from 
  in
    VNeutral transTgt (NReplace neu (Normal motT mot) (Normal baseT base))
doReplace eq mot base = tyCheckError "doReplace" [eq, mot, base]




indNatStepType :: Value -> Value
indNatStepType mot =
  eval (Env [("mot", mot)])
    (Pi "n-1" Nat
      (Pi "ind"
         (App (Var "mot") (Var "n-1"))
         (App (Var "mot") (Add1 (Var "n-1"))
         )
      )
    )
      
doIndNatStep :: Value -> Value -> Value -> Value -> Value
doIndNatStep VZero _ base _ = base
doIndNatStep (VAdd1 nV) mot base step =
  doApply (doApply step nV) (doIndNatStep nV mot base step)
doIndNatStep tgt@(VNeutral VNat neu) mot base step =
  let
    indT  = indNatStepType mot
    motT  = VPi VNat (Closure emptyEnv newVar U)
    baseT = doApply mot VZero
  in
    VNeutral (doApply mot tgt)
      (NIndNat neu
       (Normal motT mot)
       (Normal baseT base)
       (Normal indT step)
      )
doIndNatStep nVal mot base step = tyCheckError "doIndNatStep" [nVal, mot, base, step]


readBackNormal :: Ctx -> Normal -> Expr
readBackNormal ctx (Normal t v) = readBackTyped ctx t v


readBackTyped :: Ctx -> Ty -> Value -> Expr
readBackTyped ctx VNat VZero = Zero
readBackTyped ctx VNat (VAdd1 nV) = Add1 (readBackTyped ctx VNat nV)
readBackTyped ctx (VPi domT depT) fun =
  let
    var    = freshen ctx (getClosureName depT)
    varVal = undefined
  in
    
    Lam var
      (readBackTyped
        (extendCtx ctx var domT)
        (evalClosure depT varVal)
        (doApply fun varVal)
      )
readBackTyped ctx (VSigma carT cdrT) pair =
  let
    carV = doCar pair
    cdrV = doCdr pair
    depT = evalClosure cdrT carV
  in
    Cons (readBackTyped ctx carT carV) (readBackTyped ctx depT cdrV)
readBackTyped ctx VTrivial _ = Sole
readBackTyped ctx VAbsurd (VNeutral VAbsurd neu) =
  The Absurd (readBackNeutral ctx neu)
readBackTyped ctx (VEq _ _ _) VSame = Same
readBackTyped ctx VAtom (VTick chars) = Tick chars
readBackTyped ctx VU VNat = Nat
readBackTyped ctx VU VTrivial = Trivial
readBackTyped ctx VU VAbsurd  = Absurd
readBackTyped ctx VU VAtom    = Atom
-- This needs to change when universes are added
readBackTyped ctx VU VU = U
readBackTyped ctx VU (VEq t from to) =
  Equal
    (readBackTyped ctx VU t)
    (readBackTyped ctx t from)
    (readBackTyped ctx t to)
readBackTyped ctx VU (VSigma carT cdrT) =
  let
    var     = freshen ctx (getClosureName cdrT)
    varVal  = VNeutral carT (NVar var)
    cdrVal  = evalClosure cdrT varVal
    cdrTFin = readBackTyped (extendCtx ctx var carT) VU cdrVal
    carTFin = readBackTyped ctx VU carT
  in
    Sigma var carTFin cdrTFin
readBackTyped ctx VU (VPi domT depT) =
  let
    var     = freshen ctx (getClosureName depT)
    varVal  = VNeutral domT (NVar var)
    depTVal = evalClosure depT varVal
    depTFin = readBackTyped (extendCtx ctx var domT) VU depTVal
    domTFin = readBackTyped ctx VU domT
  in
    Pi var domTFin depTFin
readBackTyped ctx _ (VNeutral _ neu) = readBackNeutral ctx neu
readBackTyped ctx ty val = readBackError "readBackTyped" ty val


readBackNeutral :: Ctx -> Neutral -> Expr
readBackNeutral = undefined


tyCheckError :: String -> [Value] -> Value
tyCheckError funName vals = error $
  unlines $
    [ "Internal error (" <> funName <> "): typecheckerError"
    ] <>
    map show vals

readBackError :: String -> Value -> Value -> Expr
readBackError funName ty val = error $
  unlines $
    [ "Internal error (" <> funName <> "): typecheckerError"
    , "value: " <> show val
    , "wrong type: " <> show ty
    ] 
