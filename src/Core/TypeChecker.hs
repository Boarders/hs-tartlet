{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Core.TypeChecker where

import Core.Expression

import Core.Eval

import Control.Applicative
import Control.Monad.Except

data TyCheckError =
  TyCheckError

lookupLoc :: MonadError TyCheckError m => LocalEnv -> Int -> m Ty
lookupLoc env i = pure $ env !! i

lookupTop :: MonadError TyCheckError m => TopEnv -> Name -> m Ty
lookupTop [] v = throwError TyCheckError
lookupTop ((x,ty) : env) v
  | x == v = pure . normalTy $ ty
  | otherwise = lookupTop env v


check :: MonadError TyCheckError m => Ctx -> Expr -> Ty -> m ()
check = undefined

conv :: MonadError TyCheckError m => Ctx -> (Ty, (Value, Value)) -> m ()
conv ctx@(topEnv, locEnv) = \case
  (VU, (VU, VU)) -> pure ()
  (VU, ((VPi _ dom1 dep1), (VPi _ dom2 dep2))) ->
    let
      var = VNeutral dom1 (NVar 0)
    in
      do
        conv ctx (VU, (dom1, dom2))
        conv (topEnv, extendEnv locEnv dom1) (VU, ((dep1 var), (dep2 var)))
  ((VPi _ a b), (VLam _ bod1, VLam _ bod2)) ->
    let
      var = VNeutral a (NVar 0)
    in
      conv (topEnv, extendEnv locEnv a) ((b var), ((bod1 var), (bod2 var)))
  (VSigma _ tyCar tyCdr, (VPair car1 cdr1, VPair car2 cdr2)) ->
    do
      conv ctx (tyCar, (car1, car2))
      let
        newCtx = (topEnv, extendEnv locEnv car1)
      conv newCtx (tyCdr car1, (cdr1, cdr2))
  (VU, (VNat, VNat)) -> pure ()
  (VNat, (VZero, VZero)) -> pure ()
  (VNat, (VAdd1 n1, VAdd1 n2)) -> conv ctx (VNat, (n1, n2))
  (VEqual _ _ _, (VSame, VSame)) -> pure ()
  (VTrivial, (_,_)) -> pure ()
  (VAbsurd, (_,_)) -> pure ()
  (VAtom, (VTick chrs1, VTick chrs2)) | chrs1 == chrs2 -> pure ()
  (ty, (VTop _ neu1 _ val1, VTop _ neu2 _ val2)) ->
    do
      neuConv ctx (ty, (neu1, neu2))
      conv ctx (ty, (val1, val2))
  (ty, (VNeutral _ neu1, VNeutral _ neu2)) ->
    neuConv ctx (ty, (neu1, neu2))
  




neuConv :: MonadError TyCheckError m => Ctx -> (Ty, (Neutral, Neutral)) -> m ()
neuConv = undefined


  

synth :: MonadError TyCheckError m => Ctx -> Expr -> m Ty
synth ctx@(topEnv, locEnv) =
  \case
--      (v : A) ∈ Γ
--      -----------
--       Γ |- v : A
     Loc n -> do
       lookupLoc locEnv n
     Top n -> do
       lookupTop topEnv n

--    Γ |- A <= U;   Γ, x:A |- B <= U
--   --------------------------------
--        Γ |- (x : A) -> B => U
     (Pi n dom dep) -> do
       check ctx dom VU
       check (topEnv, extendEnv locEnv (eval topEnv locEnv dom)) dep VU
       pure VU

--    Γ |- fn => (x : A) -> B;   Γ |- arg <= A
--   ---------------------------------------------
--        Γ |- (fn arg) => B[arg/x]
     (App fn arg) -> do
       fnTy <- synth ctx fn
       case fnTy of
         (VPi n dom dep) -> do
           check ctx arg dom
           pure (dep (eval topEnv locEnv arg))
         _ -> throwError TyCheckError

--    Γ |- A <= U;   Γ, x : A |- B <= U
--   ---------------------------------------------
--        Γ |- (x : A) * B  => U
     (Sigma n car cdr) -> do
       check ctx car VU
       check (topEnv, extendEnv locEnv (eval topEnv locEnv car)) cdr VU
       pure VU
       
--      Γ |- p => (x : A) * B
--   --------------------------
--        Γ |- car p  => A
     (Car p) -> do
       t <- synth ctx p
       case t of
         (VSigma _ car _) -> pure car
         _                -> throwError TyCheckError
         
--        Γ |- p => (x : A) * B
--   -------------------------------
--        Γ |- cdr p  => B [car p/x]
     (Car p) -> do
       t <- synth ctx p
       case t of
         (VSigma n _ cdr) -> pure $ (cdr (doCar (eval topEnv locEnv p)))
         _                -> throwError TyCheckError
     
           
       
       
