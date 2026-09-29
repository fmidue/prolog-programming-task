module Prolog.Programming.CodeAnalysis.Rules.GroupedDefinitions (groupedDefinitionChecker) where

import Data.List (sort)
import Data.List.Extra (groupOn)
import Data.Maybe (mapMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string)

-- TODO: Annahme ist, dass parser Reihenfolge nicht verändert -> sollte auf jeden Fall ein Test Case sein

groupedDefinitionChecker :: ProgramRule
groupedDefinitionChecker clauses = [problem | groupNames /= sort groupNames]
  where
    groupedByName = groupOn (structName . lhs) clauses
    groupNames = mapMaybe (structName . lhs . head) groupedByName

structName :: Term -> Maybe String
structName (Struct name _) = Just name
structName _ = Nothing

problem :: Problem
problem =
  Problem {
    problemDisplay = string $ pack "Your code does not group predicate definitions my predicate name."
    }
