{-# LANGUAGE RecordWildCards #-}

module Prolog.Programming.CodeAnalysis.Rules.ClauseAmount (clauseAmountChecker) where

import Data.Text.Lazy (pack)
import Prolog.Programming.CodeAnalysis.Types (BoundsConfig (BoundsConfig, lowerBound, upperBound), Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string)

clauseAmountChecker :: BoundsConfig -> ProgramRule
clauseAmountChecker BoundsConfig {..} clauses = case lowerBound of
  Just lower | length clauses < lower -> [toProblem "Your program has too few clauses."]
  _ -> case upperBound of
    Just upper | length clauses > upper -> [toProblem "Your program has too many clauses."]
    _ -> []

toProblem :: String -> Problem
toProblem msg =
  Problem {
    problemDisplay = string $ pack msg
    }
