{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict            #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE BlockArguments    #-}
module Core.Eval.MetaLang.Eval where

import Core.Expression
import Core.Eval.MetaLang.Value
import Control.Monad (join)
import Data.List (elemIndex)

-- In our syntax we use de-bruijn indices but in our evaluator we use de-bruijn levels,
-- this means the eval function uses indices but the readback uses levels.


conv' :: Ty -> LocalEnv -> Value -> Value -> Bool
conv' ty locEnv val1 val2 =
  let
    e1 = readBackTyped locEnv 0 val1 ty
    e2 = readBackTyped locEnv 0 val2 ty
  in
    e1 == e2
    
    
     
eval :: TopEnv -> LocalEnv -> Expr -> Value
eval topEnv locEnv =
  let
    localEval = eval topEnv locEnv
    binderEval var body val = eval topEnv (extendEnv locEnv val) body
  in
  \case
    (Loc v) -> evalLocVar locEnv v
    (Top v) -> evalTopVar topEnv v
    (Pi n dom dep) -> VPi n (localEval dom) \val -> binderEval n dep val
    (Lam n body) -> VLam n \val -> eval topEnv (extendEnv locEnv val) body
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


evalLocVar :: LocalEnv -> Int -> Value
evalLocVar locEnv depth = locEnv !! depth


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

lookupLocError :: String -> Int -> Value
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
-- could write this out explicitly?
  eval [] [mot]
    (Pi "n-1" Nat
      (Pi "ind"
         (App (Var 2) (Var 1))
         (App (Var 2) (Add1 (Var 1))
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


readBackNormal :: LocalEnv -> Int -> Normal -> Expr
readBackNormal locEnv depth (Normal t v) = readBackTyped locEnv depth t v


-- Here the depth refers to a variable which is not under any binder, this starts at 1 and increases as we pass under any binder. This gives us a source of fresh variables.
readBackTyped :: LocalEnv -> Int -> Ty -> Value -> Expr
readBackTyped _ _ VNat VZero = Zero
readBackTyped locEnv depth VNat (VAdd1 nV) = Add1 (readBackTyped locEnv depth VNat nV)
readBackTyped locEnv depth (VPi n domT depT) fun@(VLam name _) =
  let
    fresh  = depth + 1
    varVal = VNeutral domT (NVar fresh)
  in
    Lam name
      (readBackTyped
        locEnv
        fresh
        (depT varVal)
        (doApply fun varVal)
      )
readBackTyped locEnv depth (VSigma n carT cdrT) pair =
  let
    carV = doCar pair
    cdrV = doCdr pair
    depT = cdrT carV
  in
    Cons (readBackTyped locEnv depth carT carV) (readBackTyped locEnv depth depT cdrV)
readBackTyped _ depth VTrivial _ = Sole
readBackTyped locEnv depth VAbsurd (VNeutral VAbsurd neu) =
  The Absurd (readBackNeutral locEnv depth neu)
readBackTyped locEnv depth (VEqual _ _ _) VSame = Same
readBackTyped locEnv depth VAtom (VTick chars) = Tick chars
readBackTyped locEnv depth VU VNat = Nat
readBackTyped locEnv depth VU VTrivial = Trivial
readBackTyped locEnv depth VU VAbsurd  = Absurd
readBackTyped locEnv depth VU VAtom    = Atom
-- This needs to change when universes are added
readBackTyped locEnv depth VU VU = U
readBackTyped locEnv depth VU (VEqual t from to) =
  Equal
    (readBackTyped locEnv depth VU t)
    (readBackTyped locEnv depth t from)
    (readBackTyped locEnv depth t to)
readBackTyped locEnv depth VU (VSigma n carT cdrT) =
  let
    fresh   = depth + 1
    varVal  = VNeutral carT (NVar fresh)
    cdrVal  = cdrT varVal
    cdrTFin = readBackTyped locEnv fresh VU cdrVal
    carTFin = readBackTyped locEnv depth VU carT
  in
    Sigma n carTFin cdrTFin
readBackTyped locEnv depth VU (VPi n domT depT) =
  let
    fresh     = depth + 1
    varVal  = VNeutral domT (NVar fresh)
    depTVal = depT varVal
    depTFin = readBackTyped locEnv fresh VU depTVal
    domTFin = readBackTyped locEnv depth VU domT
  in
    Pi n domTFin depTFin
readBackTyped locEnv depth _ (VNeutral _ neu) = readBackNeutral locEnv depth neu
readBackTyped _ _ ty val = readBackError "readBackTyped" ty val



readBackNeutral :: LocalEnv -> Int -> Neutral -> Expr
readBackNeutral locEnv depth =
  let
    localReadNeutral = readBackNeutral locEnv depth
    localReadNormal  = readBackNormal  locEnv depth
  in \case
               -- Convert debruijn level to debruijn index
  (NVar i) -> Var (depth - i - 1)
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
      (The Absurd (readBackNeutral locEnv depth absurd))
      (readBackNormal locEnv depth ty)


readBackError :: String -> Value -> Value -> Expr
readBackError funName ty val = error $
  unlines $
    [ "Internal error (" <> funName <> "): typecheckerError"
    ]
