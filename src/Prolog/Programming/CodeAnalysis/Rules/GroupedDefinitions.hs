module Prolog.Programming.CodeAnalysis.Rules.GroupedDefinitions (groupedDefinitionChecker) where

import Data.List (sort)
import Data.List.Extra (groupOn)
import Data.Maybe (mapMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string)

groupedDefinitionChecker :: ProgramRule
groupedDefinitionChecker clauses =
  [problem "Your code does not group predicate definitions by predicate name." | groupNames /= sort groupNames]
    ++ [ problem "Your code does not sort the predicate definitions ascending by arity (per group)."
       | any (\g -> let x = mapMaybe (structName . lhs) g in x /= sort x) groupedByName
       ]
  where
    groupedByName = groupOn (fmap fst . structName . lhs) clauses
    groupNames = mapMaybe (fmap fst . structName . lhs . head) groupedByName

structName :: Term -> Maybe (String, Int)
structName (Struct name args) = Just (name, length args)
structName _ = Nothing

problem :: String -> Problem
problem msg =
  Problem {
    problemDisplay = string $ pack msg
    }
