module Prolog.Programming.CodeAnalysis.Rules.UngroupedDefinitions (ungroupedDefinitionsChecker) where

import Data.List.Extra (anySame, groupOn)
import Data.List.Ordered (isSorted)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Text.Lazy (pack)
import Prolog.Programming.CodeAnalysis.Helper (clauseIdentities)
import Prolog.Programming.CodeAnalysis.Types (Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string)

ungroupedDefinitionsChecker :: ProgramRule
ungroupedDefinitionsChecker clauses =
  [toProblem "Your code does not group predicate definitions by predicate name." | duplicateExists]
    ++ [ toProblem "Your code does not sort the predicate definitions ascending by arity (per group)."
       | not (all (isSorted . map snd) groupedByName)
       ]
  where
    groupedByName = groupOn fst $ map (fst . clauseIdentities) clauses
    groupNames = mapMaybe ((fst <$>) . listToMaybe) groupedByName
    duplicateExists = anySame groupNames

toProblem :: String -> Problem
toProblem msg =
  Problem {
    problemDisplay = string $ pack msg
    }
