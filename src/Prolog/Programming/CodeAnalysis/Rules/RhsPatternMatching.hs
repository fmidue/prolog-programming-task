module Prolog.Programming.CodeAnalysis.Rules.RhsPatternMatching (rhsPatternMatchingChecker) where

import qualified Data.Map as Map (Map, keys, lookup)
import Data.Maybe (mapMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (
  Clause (..),
  Term (..),
  VariableName (VariableName),
  apply,
  unify,
 )
import Prolog.Programming.CodeAnalysis.Helper (countVariables)
import Prolog.Programming.CodeAnalysis.Types (ClauseRule, Problem (..))
import Text.PrettyPrint.Leijen.Text (indent, string, vsep)

rhsPatternMatchingChecker :: ClauseRule
rhsPatternMatchingChecker clause@(Clause (Struct _ args) rhs@(term : _)) =
  [toProblem clause term | isPatternMatch lhsVariables rhsVariableCounts term]
  where
    lhsVariables = Map.keys $ countVariables args
    rhsVariableCounts = countVariables rhs
rhsPatternMatchingChecker _ = []

isPatternMatch :: [String] -> Map.Map String Int -> Term -> Bool
isPatternMatch lhsVariables rhsVariableCounts (Struct "=" args) =
  case filter (`elem` lhsVariables) $ mapMaybe variableName args of
    variable : _ -> Map.lookup variable rhsVariableCounts == Just 1
    [] -> False
isPatternMatch _ _ _ = False

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
        , string $ pack "uses pattern-matching on the right-hand side of the clause using term"
        , indent 2 $ string $ pack $ show term
        , string $ pack "that can be moved to the left-hand side. Doing that would result in"
        , indent 2 $ string $ pack $ show $ fixedClause clause term
        ]
    }

fixedClause :: Clause -> Term -> Clause
fixedClause (Clause headTerm (_ : rhs)) (Struct "=" [left, right]) =
  case unify left right of
    Just unifier ->
      Clause
        (apply unifier headTerm)
        (map (apply unifier) rhs)
    Nothing -> error "Pattern-matching equality should always be unifiable."
fixedClause _ _ = error "Pattern-matching term should be an equality."
