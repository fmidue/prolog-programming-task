module Prolog.Programming.CodeAnalysis.Rules.UngroupedDefinitions (ungroupedDefinitionsChecker) where

import Data.List.Extra (anySame, groupOn)
import Data.List.Ordered (isSorted)
import Data.Maybe (mapMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string)

ungroupedDefinitionsChecker :: ProgramRule
ungroupedDefinitionsChecker clauses =
  [toProblem "Your code does not group predicate definitions by predicate name." | duplicateExists]
    ++ [ toProblem "Your code does not sort the predicate definitions ascending by arity (per group)."
       | not (all isSorted groupedByName)
       ]
  where
    termIdentities = mapMaybe (termIdentity . lhs) clauses
    groupedByName = groupOn fst termIdentities
    groupNames = map (fst . head) groupedByName
    duplicateExists = anySame groupNames

termIdentity :: Term -> Maybe (String, Int)
termIdentity (Struct name args) = Just (name, length args)
termIdentity _ = Nothing

toProblem :: String -> Problem
toProblem msg =
  Problem {
    problemDisplay = string $ pack msg
    }
