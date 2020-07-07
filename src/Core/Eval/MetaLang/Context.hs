{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE RecordWildCards      #-}

module Core.Eval.MetaLang.Context where

import Core.Expression
import Core.Eval.EnvMachine.Value
import qualified Core.Expression as Exp
import Control.Monad.Except
import Data.Monoid
import Data.Foldable
import Control.Applicative
import Data.String

data ConError =
  LookupError Name

-- |
-- A snoc list
data Bwd a where
  Nil  :: Bwd a
  Snoc :: Bwd a -> a -> Bwd a
  deriving stock (Eq, Functor, Foldable)

fromList :: [a] -> Bwd a
fromList = foldl' Snoc Nil

infixl 5 :|>
pattern (:|>) :: Bwd a -> a -> Bwd a
pattern xs :|> x <- Snoc xs x
  where
    xs :|> x = Snoc xs x
{-# COMPLETE Nil, (:|>) #-}


data CtxEntry = Def Ty Value | IsA Ty

type Ctx = Bwd (Name, CtxEntry)


initCtx :: Ctx
initCtx = Nil

extendCtx :: Ctx -> Name -> Ty -> Ctx
extendCtx ctx name ty = ctx :|> (name, (IsA ty))

define :: Ctx -> Name -> Ty -> Value -> Ctx
define ctx name ty val = ctx :|> (name, (Def ty val))

lookupType :: MonadError ConError m => Ctx -> Name -> m Ty
lookupType Nil x = throwError (LookupError x)
lookupType (ctx :|> (y, conEntry)) x
  | x == y =
    case conEntry of
      Def ty _ -> pure ty
      IsA ty   -> pure ty
  | otherwise = lookupType ctx x


{-

findMaxId :: Ctx -> String -> Maybe Int
findMaxId ctx str = go Nothing ctx
  where
    go acc Nil = acc
    go acc (xs :|> (Name{..}, _)) | str == name = go (liftA2 max acc (Just iD)) xs
                           | otherwise = go acc xs
             
freshen :: Ctx -> String -> Name
freshen ctx str =
  case findMaxId ctx str  of
    Nothing -> fromString str
    Just k  -> Name (k + 1) str
-}
