{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Core.TypeChecker where

import Core.Expression

import Core.Eval

import Control.Applicative
import Control.Monad.Except

data TyCheckError =
  TyCheckError

lookupLoc :: MonadError TyCheckError m => LocalEnv -> Name -> m Ty
lookupLoc [] v = throwError TyCheckError
lookupLoc ((x,ty) : env) v
  | x == v = pure ty
  | otherwise = lookupLoc env v

lookupTop :: MonadError TyCheckError m => TopEnv -> Name -> m Ty
lookupTop [] v = throwError TyCheckError
lookupTop ((x,ty) : env) v
  | x == v = pure . normalTy $ ty
  | otherwise = lookupTop env v  
                           
  
  

synth :: MonadError TyCheckError m => Ctx -> Expr -> m Ty
synth (locEnv, topEnv) =
  \case
--      (v : A) ∈ Γ
--      -----------
--       Γ |- v : A
     Loc n -> do
       lookupLoc locEnv n
     Top n -> do
       lookupTop topEnv n       
--    Γ |- A <= U,   Γ, x:A |- B <= U
--   --------------------------------
--        Γ |- (x : A) -> B => U       
        
        
