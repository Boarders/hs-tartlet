{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}
module Core.Parser.SrcLoc where

import Core.Parser.Token
import Data.Text (Text)
import qualified Data.Text as Text


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

tokSrcPos :: Token -> SrcPos
tokSrcPos = srcPos . getPos

getSrcText :: Int -> Int -> SrcPos -> Text -> Text
getSrcText maxLine _ (SrcPos _ line col) t = textStart
  where
    textLine :: Text
    textLine = ((!! (line - 1)) . Text.lines) $ t

    leftBuffer = col

    textStart :: Text
    textStart
      | Text.length textLine <= maxLine = textLine
      | otherwise =
          Text.take maxLine (Text.drop (leftBuffer - 1) textLine)
