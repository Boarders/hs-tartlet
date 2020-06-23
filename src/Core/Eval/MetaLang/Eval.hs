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
    (Pi n dom dep) -> VPi n (localEval dom) \val -> binderEval n dep val
    (Lam n body) -> VLam n \val -> eval topEnv (extendEnv locEnv n val) body
    (App fn arg) -> doApply (localEval fn) (localEval arg)
    (Sigma a carT cdrT) ->
      VSigma a (localEval carT) \val -> binderEval a cdrT val
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
doApply (VNeutral (VPi _ domT depT) neu) ~arg =
  let
    subDepT = depT arg
  in
    VNeutral subDepT (NApp neu (Normal domT arg))
doApply (VTop v neu (VPi _ domT depT) val) ~arg =
  let
    subDepT = depT arg
  in
    VTop v (NApp neu (Normal domT arg)) subDepT (doApply val arg)
doApply fun arg = tyCheckError "doApply" [fun, arg]


doCar :: Value -> Value
doCar (VPair f _) = f
doCar (VNeutral (VSigma _ domT _) neu) = VNeutral domT (NCar neu)
doCar val = tyCheckError "doCar" [val]

doCdr :: Value -> Value
doCdr (VPair _ s) = s
doCdr neuV@(VNeutral (VSigma _ _ depT) neu) =
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
    motT     = VPi "_" ty \_ -> VU
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
    motT  = VPi "_" VNat \_ -> VU
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


readBackNormal :: LocalEnv -> TopEnv -> Normal -> Expr
readBackNormal locEnv topEnv (Normal t v) = readBackTyped locEnv topEnv t v


readBackTyped :: LocalEnv -> TopEnv -> Ty -> Value -> Expr
readBackTyped _ _ VNat VZero = Zero
readBackTyped locEnv topEnv VNat (VAdd1 nV) = Add1 (readBackTyped locEnv topEnv VNat nV)
readBackTyped locEnv topEnv (VPi n domT depT) fun =
  let
    var    = freshen locEnv (name n)
    varVal = undefined
  in
    Lam var
      (readBackTyped
        (extendEnv locEnv var domT)
        topEnv
        (depT varVal)
        (doApply fun varVal)
      )
readBackTyped locEnv topEnv (VSigma n carT cdrT) pair =
  let
    carV = doCar pair
    cdrV = doCdr pair
    depT = cdrT carV
  in
    Cons (readBackTyped locEnv topEnv carT carV) (readBackTyped locEnv topEnv depT cdrV)
readBackTyped locEnv topEnv VTrivial _ = Sole
readBackTyped locEnv topEnv VAbsurd (VNeutral VAbsurd neu) =
  The Absurd (readBackNeutral locEnv topEnv neu)
readBackTyped locEnv topEnv (VEqual _ _ _) VSame = Same
readBackTyped locEnv topEnv VAtom (VTick chars) = Tick chars
readBackTyped locEnv topEnv VU VNat = Nat
readBackTyped locEnv topEnv VU VTrivial = Trivial
readBackTyped locEnv topEnv VU VAbsurd  = Absurd
readBackTyped locEnv topEnv VU VAtom    = Atom
-- This needs to change when universes are added
readBackTyped locEnv topEnv VU VU = U
readBackTyped locEnv topEnv VU (VEqual t from to) =
  Equal
    (readBackTyped locEnv topEnv VU t)
    (readBackTyped locEnv topEnv t from)
    (readBackTyped locEnv topEnv t to)
readBackTyped locEnv topEnv VU (VSigma n carT cdrT) =
  let
    var     = freshen locEnv (name n)
    varVal  = VNeutral carT (NVar var)
    cdrVal  = cdrT varVal
    cdrTFin = readBackTyped (extendEnv locEnv var carT) topEnv VU cdrVal
    carTFin = readBackTyped locEnv topEnv VU carT
  in
    Sigma var carTFin cdrTFin
readBackTyped locEnv topEnv VU (VPi n domT depT) =
  let
    var     = freshen locEnv (name n)
    varVal  = VNeutral domT (NVar var)
    depTVal = depT varVal
    depTFin = readBackTyped (extendEnv locEnv var domT) topEnv VU depTVal
    domTFin = readBackTyped locEnv topEnv VU domT
  in
    Pi var domTFin depTFin
readBackTyped locEnv topEnv _ (VNeutral _ neu) = readBackNeutral locEnv topEnv neu
readBackTyped locEnv topEnv ty val = readBackError "readBackTyped" ty val



readBackNeutral :: LocalEnv -> TopEnv -> Neutral -> Expr
readBackNeutral locEnv topEnv =
  let
    localReadNeutral = readBackNeutral locEnv topEnv
    localReadNormal = readBackNormal  locEnv topEnv
  in \case

  (NVar v) -> Var v
  (NApp f a) -> App (localReadNeutral f) (localReadNormal a)
  (NCar neu) -> Car (localReadNeutral neu)
  (NCdr neu) -> Cdr (localReadNeutral neu)
  (NIndNat n mot base step) ->
    IndNat
      (localReadNeutral n)
      (localReadNormal mot)
      (localReadNormal base)
      (localReadNormal step)
  (NReplace eq mot base) ->
    Replace
      (localReadNeutral eq)
      (localReadNormal mot)
      (localReadNormal base)
  (NIndAbsurd absurd ty) ->
    IndAbsurd
      (The Absurd (readBackNeutral locEnv topEnv absurd))
      (readBackNormal locEnv topEnv ty)


readBackError :: String -> Value -> Value -> Expr
readBackError funName ty val = error $
  unlines $
    [ "Internal error (" <> funName <> "): typecheckerError"
    ]
