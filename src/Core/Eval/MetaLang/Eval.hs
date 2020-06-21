{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict            #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE BlockArguments    #-}
module Core.Eval.MetaLang.Eval where

import Core.Expression
import Core.Eval.MetaLang.Value
import Control.Monad (join)

eval :: TopEnv -> LocalEnv -> Expr -> Value
eval topEnv locEnv =
  let
    localEval = eval topEnv locEnv
    binderEval var body val = eval topEnv (extendEnv locEnv var val) body
  in
  \case
    (Loc v) -> evalLocVar locEnv v
    (Top v) -> evalTopVar topEnv v
    (Pi n dom dep) -> VPi (localEval dom) \val -> binderEval n dep val
    (Lam n body) -> VLam n \val -> eval topEnv (extendEnv locEnv n val) body
    (App fn arg) -> doApply (localEval fn) (localEval arg)
    (Sigma a carT cdrT) ->
      VSigma (localEval carT) \val -> binderEval a cdrT val
    (Cons f s) -> VPair (localEval f) (localEval s)
    (Car p) -> doCar (localEval p)
    (Cdr p) -> doCdr (localEval p)
    Nat -> VNat
    Zero -> VZero
    (Add1 n) -> VAdd1 (localEval n)
    (IndNat tgt mot base step)
      -> doIndNatStep (localEval tgt) (localEval mot) (localEval base) (localEval step)
    (Equal ty from to)
      -> VEqual (localEval ty) (localEval from) (localEval to)
    Same -> VSame
    (Replace eq mot base) ->
      doReplace (localEval eq) (localEval mot) (localEval base)
    Trivial -> VTrivial
    Sole -> VSole
    Absurd -> VAbsurd
    (IndAbsurd false ty) -> doIndAbsurd (localEval false) (localEval ty)
    Atom -> VAtom
    (Tick chrs) -> VTick chrs
    U -> VU
    (The _ e) -> eval topEnv locEnv e

  

evalLocVar :: LocalEnv -> Name -> Value
evalLocVar locEnv name = maybe (lookupLocError "evalLocVar" name) id  . join $ lookup name locEnv


evalTopVar :: TopEnv -> Name -> Value
evalTopVar topEnv name =
  let
    ~normal = (maybe (lookupTopError "evalLocVar" name) id $ lookup name topEnv)
    ~val    = normalVal normal
    ~ty     = normalTy  normal
    spine   = NTop name
  in
    VTop name spine ty val

lookupTopError :: String -> Name -> Normal
lookupTopError funName name = error $
  unlines
    [ "Internal error (" <> funName <> "): lookupError"
    , show name
    ]

lookupLocError :: String -> Name -> Value
lookupLocError funName name = error $
  unlines
    [ "Internal error (" <> funName <> "): lookupError"
    , show name
    ]    
    

tyCheckError :: String -> [Value] -> Value
tyCheckError funName vals = error $
  unlines $
    [ "Internal error (" <> funName <> "): typecheckerError"
    ]

doApply :: Value -> Value -> Value
doApply (VLam _ fn) ~arg = fn arg
doApply (VNeutral (VPi domT depT) neu) ~arg =
  let
    subDepT = depT arg
  in
    VNeutral subDepT (NApp neu (Normal domT arg))
doApply (VTop v neu (VPi domT depT) val) ~arg =
  let
    subDepT = depT arg
  in
    VTop v (NApp neu (Normal domT arg)) subDepT (doApply val arg)
doApply fun arg = tyCheckError "doApply" [fun, arg]


doCar :: Value -> Value
doCar (VPair f _) = f
doCar (VNeutral (VSigma domT _) neu) = VNeutral domT (NCar neu)
doCar val = tyCheckError "doCar" [val]

doCdr :: Value -> Value
doCdr (VPair _ s) = s
doCdr neuV@(VNeutral (VSigma _ depT) neu) =
  let
    subDepT = depT (doCar neuV)
  in
    VNeutral subDepT (NCdr neu)
doCdr val = tyCheckError "doCdr" [val]





doIndAbsurd :: Value -> Value -> Value
doIndAbsurd (VNeutral VAbsurd neu) mot =
  VNeutral mot (NIndAbsurd neu (Normal VU mot))
doIndAbsurd v mot = tyCheckError "doIndAbsurd" [v, mot]


doReplace :: Value -> Value -> Value -> Value
doReplace VSame _ base = base
doReplace (VNeutral (VEqual ty from to) neu) mot base =
  let
    transTgt = doApply mot to
    motT     = VPi ty \_ -> VU
    baseT    = doApply motT from 
  in
    VNeutral transTgt (NReplace neu (Normal motT mot) (Normal baseT base))
doReplace eq mot base = tyCheckError "doReplace" [eq, mot, base]




indNatStepType :: Value -> Value
indNatStepType mot =
  eval [] [("mot", Just mot)]
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
    motT  = VPi VNat \_ -> VU
    baseT = doApply mot VZero
  in
    VNeutral (doApply mot tgt)
      (NIndNat neu
       (Normal motT mot)
       (Normal baseT base)
       (Normal indT step)
      )
doIndNatStep nVal mot base step = tyCheckError "doIndNatStep" [nVal, mot, base, step]


quoteNeutral :: LocalEnv -> Bool -> Expr -> Neutral -> Expr
quoteNeutral = undefined

{-
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
readBackTyped ctx (VEqual _ _ _) VSame = Same
readBackTyped ctx VAtom (VTick chars) = Tick chars
readBackTyped ctx VU VNat = Nat
readBackTyped ctx VU VTrivial = Trivial
readBackTyped ctx VU VAbsurd  = Absurd
readBackTyped ctx VU VAtom    = Atom
-- This needs to change when universes are added
readBackTyped ctx VU VU = U
readBackTyped ctx VU (VEqual t from to) =
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
readBackNeutral ctx (NVar v) = Var v
readBackNeutral ctx (NApp f a) = App (readBackNeutral ctx f) (readBackNormal ctx a)
readBackNeutral ctx (NCar neu) = Car (readBackNeutral ctx neu)
readBackNeutral ctx (NCdr neu) = Cdr (readBackNeutral ctx neu)
readBackNeutral ctx (NIndNat n mot base step) =
  IndNat
    (readBackNeutral ctx n)
    (readBackNormal ctx mot)
    (readBackNormal ctx base)
    (readBackNormal ctx step)
readBackNeutral ctx (NReplace eq mot base) =
  Replace
    (readBackNeutral ctx eq)
    (readBackNormal ctx mot)
    (readBackNormal ctx base)
readBackNeutral ctx (NIndAbsurd absurd ty) =
  IndAbsurd
    (The Absurd (readBackNeutral ctx absurd))
    (readBackNormal ctx ty)




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


-}
