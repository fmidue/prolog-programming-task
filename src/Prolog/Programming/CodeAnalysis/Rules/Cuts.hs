{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.Cuts (cutsChecker) where

import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..))
import Prolog.Programming.CodeAnalysis.Helper (containsCut)
import Prolog.Programming.CodeAnalysis.Types (AdditionalMessage (..), ClauseRule, Problem (..))
import Text.PrettyPrint.Leijen.Text (empty, indent, linebreak, string, vsep)

cutsChecker :: AdditionalMessage -> ClauseRule
cutsChecker (AdditionalMessage cMsg) (name, args, goals)
  | any containsCut goals = [toProblem cMsg $ Clause name args goals]
  | otherwise = []

toProblem :: Maybe String -> Clause -> Problem
toProblem cMsg clause =
  Problem {
    problemDisplay =
      vsep
        [ string "Your clause"
        , indent 2 $ string $ pack $ show clause
        , string "makes use of the cut (!) operator." <> linebreak
        , maybe empty (string . pack) cMsg
        ]
    }
