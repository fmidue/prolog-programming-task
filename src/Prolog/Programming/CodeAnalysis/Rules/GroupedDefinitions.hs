module Prolog.Programming.CodeAnalysis.Rules.GroupedDefinitions (groupedDefinitionChecker) where

import Data.List (sort)
import Data.List.Extra (groupOn, nubOrd)
import Data.Maybe (mapMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string)

groupedDefinitionChecker :: ProgramRule
groupedDefinitionChecker clauses =
  [toProblem "Your code does not group predicate definitions by predicate name." | duplicateExists]
    ++ [ toProblem "Your code does not sort the predicate definitions ascending by arity (per group)."
       | any (\g -> let x = mapMaybe (termIdentity . lhs) g in x /= sort x) groupedByName
       ]
  where
    groupedByName = groupOn (fmap fst . termIdentity . lhs) clauses
    groupNames = mapMaybe (fmap fst . termIdentity . lhs . head) groupedByName
    duplicateExists = length groupNames /= length (nubOrd groupNames)

termIdentity :: Term -> Maybe (String, Int)
termIdentity (Struct name args) = Just (name, length args)
termIdentity _ = Nothing

toProblem :: String -> Problem
toProblem msg =
  Problem {
    problemDisplay = string $ pack msg
    }
