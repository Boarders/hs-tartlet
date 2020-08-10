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
     
           
       
       
