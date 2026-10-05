module Prolog.Programming.CodeAnalysis.Rules.RhsPatternMatching where

import qualified Data.Map as Map (Map, keys, lookup)
import Data.Maybe (mapMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..), VariableName (VariableName))
import Prolog.Programming.CodeAnalysis.Helper (containsCut, countVariables)
import Prolog.Programming.CodeAnalysis.Types (ClauseRule, Problem (..))
import Text.PrettyPrint.Leijen.Text (indent, string, vsep)

rhsPatternMatchingChecker :: ClauseRule
rhsPatternMatchingChecker clause@(Clause (Struct _ lhsTerm) rhs) =
  map (toProblem clause) patternMatches
  where
    lhsVariables = Map.keys $ countVariables lhsTerm
    rhsVariableCounts = countVariables rhs
    patternMatches = findPatternMatches False rhs

    findPatternMatches _ [] = []
    findPatternMatches cutSeen (term : terms)
      | cutSeen = []
      | isPatternMatch lhsVariables rhsVariableCounts term =
          term : findPatternMatches (containsCut term) terms
      | containsCut term = []
      | otherwise = findPatternMatches False terms
rhsPatternMatchingChecker _ = []

isPatternMatch :: [String] -> Map.Map String Int -> Term -> Bool
isPatternMatch lhsVariables rhsVariableCounts term =
  case lhsVariableInEquation lhsVariables term of
    Just variable ->
      Map.lookup variable rhsVariableCounts == Just 1
    Nothing -> False

lhsVariableInEquation :: [String] -> Term -> Maybe String
lhsVariableInEquation lhsVariables (Struct "=" [left, right]) =
  case filter (`elem` lhsVariables) $ mapMaybe variableName [left, right] of
    variable : _ -> Just variable
    [] -> Nothing
lhsVariableInEquation _ _ = Nothing

variableName :: Term -> Maybe String
variableName (Var (VariableName _ name)) = Just name
variableName _ = Nothing

toProblem :: Clause -> Term -> Problem
toProblem clause term =
  Problem {
    problemDisplay =
      vsep
        [ string $ pack "Your clause"
        , indent 2 $ string $ pack $ show clause
        , string $ pack "uses pattern-matching on the right-hand side of the clause"
        , indent 2 $ string $ pack $ show term
        , string $ pack "that can be moved to the left-hand side."
        ]
    }
