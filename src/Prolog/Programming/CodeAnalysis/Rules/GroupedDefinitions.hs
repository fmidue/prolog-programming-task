module Prolog.Programming.CodeAnalysis.Rules.GroupedDefinitions (groupedDefinitionChecker) where

import Data.List (sort)
import Data.List.Extra (anySame, groupOn)
import Data.Maybe (mapMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string)

groupedDefinitionChecker :: ProgramRule
groupedDefinitionChecker clauses =
  [toProblem "Your code does not group predicate definitions by predicate name." | duplicateExists]
    ++ [ toProblem "Your code does not sort the predicate definitions ascending by arity (per group)."
       | any (\g -> g /= sort g) groupedByName
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
