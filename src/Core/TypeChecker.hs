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
--        Γ valid
--   ----------------------
--        Γ |- Nat => U
     Nat -> do
       pure VU
--        Γ |- tgt => Nat
--        Γ |- mot  <= (Nat -> U)
--        Γ |- base <= mot zero
--        Γ |- step <= (n : Nat) -> mot n -> mot (add1 n)
--   -----------------------------------------------------
--        Γ |- (indNat tgt mot base step) => (mot tgt)
     IndNat tgt mot base step -> do
       isNat (synth ctx tgt)
       check ctx mot natMotTy
       let motV = eval topEnv locEnv mot
       let tgtV = eval topEnv locEnv tgt
       check ctx base (doApply motV VZero)
       check ctx step (indNatStepType motV)
       pure (doApply motV tgtV)
--        Γ |- A <= U
--        Γ |- from <= A
--        Γ |- to   <= A
--   -----------------------------------------------------
--        Γ |- (Eq A from to) => U
     (Equal ty from to) -> do
       check ctx ty VU
       let tyV = eval topEnv locEnv ty
       check ctx from tyV
       check ctx to   tyV
       pure VU
--        Γ |- eq => (Eq A from to)
--        Γ |- mot  <= (A -> U)
--        Γ |- base <= mot from
--   -----------------------------------------------------
--        Γ |- (trans eq mot base) => mot to
     (Replace eq mot base) -> do
       (tyV, fromV, toV) <- isEq (synth ctx eq)
       check ctx mot (eqMotTy tyV)
       let motV = eval topEnv locEnv mot
       check ctx base (doApply motV fromV)
       pure (doApply motV toV)
--        Γ valid
--   -----------------------
--        Γ |- Unit => U
     Trivial -> do
       pure VU
--        Γ valid
--   -----------------------
--        Γ |- Absurd => U
     Absurd -> do
       pure VU
--        Γ |- tgt => Absur
--        Γ |- mot <= U
--   -----------------------
--        Γ |- (ind-Absurd tgt mot) => mot
     IndAbsurd tgt mot -> do
       pure undefined
     

     
 
 


isNat :: MonadError TyCheckError m => m Ty -> m ()
isNat m = do
  ty <- m
  case ty of
    VNat -> pure ()
    _    -> throwError TyCheckError

isEq :: MonadError TyCheckError m => m Ty -> m (Ty, Value, Value)
isEq m = do
  tyV <- m
  case tyV of
    VEqual ty from to -> pure (ty, from, to)
    _ -> throwError TyCheckError


natMotTy :: Value
natMotTy = VPi dummyVar VNat (\_ -> VU)

eqMotTy :: Value -> Value
eqMotTy tyV = VPi dummyVar tyV (\_ -> VU)
