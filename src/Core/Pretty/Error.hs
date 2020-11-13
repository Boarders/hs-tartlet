{-# language LambdaCase #-}
module Core.Pretty.Error where

import Prettyprinter
import Data.Text (Text)
import qualified Data.Text as Text
import Core.Parser.SrcLoc
import Data.Foldable
import Data.Text.Prettyprint.Doc.Render.Terminal

data ErrorAttr =
    ErrorMessage
  | ErrorSrc
  | SrcLoc
  | Normal
  | ErrorType

toAnsiAttr :: ErrorAttr -> AnsiStyle
toAnsiAttr = \case
  ErrorMessage -> color Green
  ErrorSrc     -> colorDull Red
  SrcLoc       -> color Magenta
  Normal       -> color White
  ErrorType    -> color Green
  
  

printTextError :: Int -> Text -> SrcPos -> Text -> Text -> Doc ErrorAttr
printTextError maxLine input srcP@(SrcPos _ l c) errorMessage errorType =
  vsep
    [ mempty
    , errorMessageDoc
    , mempty
    , pretty bars
    , lineError
    , srcReportError
    , mempty
    , pretty c
    ]
  where
    errorMessageDoc =
      annotate ErrorMessage $
         pretty errorMessage
    preSpacesLen =
      length (show c) + 2
    postSpacesLen =
      c - 1
    preSpaces  = replicate preSpacesLen  ' '
    postSpaces = replicate postSpacesLen ' '

    bars = preSpaces ++ "|"


    lineError =
      fold
      [ annotate Normal $ pretty " "
      , annotate Normal $ pretty l
      , annotate Normal $ pretty " |"
      , annotate ErrorSrc (pretty (getSrcText maxLine 0 srcP input))
      ]

    srcReportError = annotate SrcLoc $
      fold
      [ annotate Normal $ pretty bars
      , annotate Normal $ pretty postSpaces
      , annotate SrcLoc $ pretty "^^^ "
      , annotate ErrorType  $ align (pretty errorType)
      ]
