module Prolog.Programming.CodeAnalysis.Rules.UngroupedDefinitions (ungroupedDefinitionsChecker) where

import Data.List.Extra (anySame)
import qualified Data.List.NonEmpty as NE (groupWith, head, toList)
import Data.List.Ordered (isSorted)
import Data.Text.Lazy (pack)
import Prolog.Programming.CodeAnalysis.Helper (clauseIdentities)
import Prolog.Programming.CodeAnalysis.Types (Predicate (predicateArity, predicateName), Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string)

ungroupedDefinitionsChecker :: ProgramRule
ungroupedDefinitionsChecker clauses =
  [toProblem "Your code does not group predicate definitions by predicate name." | duplicateExists]
    ++ [ toProblem "Your code does not sort the predicate definitions ascending by arity (per group)."
       | not (all (isSorted . map predicateArity . NE.toList) groupedByName)
       ]
  where
    groupedByName = NE.groupWith predicateName $ map (fst . clauseIdentities False) clauses
    duplicateExists = anySame $ map (predicateName . NE.head) groupedByName

toProblem :: String -> Problem
toProblem msg =
  Problem {
    problemDisplay = string $ pack msg
    }
