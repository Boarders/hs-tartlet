{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}
module Core.Parser.SrcLoc where

import Core.Parser.Token


newtype SrcPos = SrcPosCon {getSrcPos :: AlexPosn}
  deriving (Eq, Show)


pattern SrcPos :: Int -> Int -> Int -> SrcPos
pattern SrcPos o l c = SrcPosCon (AlexPn o l c)
{-# COMPLETE SrcPos #-}

instance Ord SrcPos where
  (<) (SrcPos o1 l1 c1) (SrcPos o2 l2 c2) =
    o1 < o2 || o1 == o2 && l1 < l2 || o1 == o2 && l1 == l2 && c1 < c2
  (<=) sp1 sp2 = sp1 < sp2 || sp1 == sp2

srcPos :: AlexPosn -> SrcPos
srcPos = SrcPosCon

data SrcSpan = SrcSpan
  { srcSpanStart :: !SrcPos
  , srcSpanEnd   :: !SrcPos
  } deriving (Eq, Ord, Show)

getSrcSpanStart :: SrcSpan -> SrcPos
getSrcSpanStart = srcSpanStart

getSrcSpanEnd :: SrcSpan -> SrcPos
getSrcSpanEnd = srcSpanEnd

getCharOffSet :: SrcPos -> Int
getCharOffSet (SrcPos o _ _) = o

getLineNo :: SrcPos -> Int
getLineNo (SrcPos _ l _) = l

getCol :: SrcPos -> Int
getCol (SrcPos _ _ c) = c
