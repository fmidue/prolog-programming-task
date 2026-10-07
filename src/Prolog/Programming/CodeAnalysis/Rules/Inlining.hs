module Prolog.Programming.CodeAnalysis.Rules.Inlining (inliningChecker) where

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

inliningChecker :: ClauseRule
inliningChecker clause@(Clause (Struct _ args) rhs@(term : _)) =
  [toProblem clause term | canBeInlinedToClauseHead lhsVariables rhsVariableCounts term]
  where
    lhsVariables = Map.keys $ countVariables args
    rhsVariableCounts = countVariables rhs
inliningChecker _ = []

canBeInlinedToClauseHead :: [String] -> Map.Map String Int -> Term -> Bool
canBeInlinedToClauseHead lhsVariables rhsVariableCounts (Struct "=" args) =
  case filter (`elem` lhsVariables) $ mapMaybe variableName args of
    variable : _ -> Map.lookup variable rhsVariableCounts == Just 1
    [] -> False
canBeInlinedToClauseHead _ _ _ = False

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
        , string $ pack "uses the term"
        , indent 2 $ string $ pack $ show term
        , string $ pack "as its first goal which can be inlined into the clause head."
        , string $ pack "That would result in:"
        , indent 2 $ string $ pack $ show $ inlinedClause clause term
        ]
    }

inlinedClause :: Clause -> Term -> Clause
inlinedClause (Clause headTerm (_ : rhs)) (Struct "=" [left, right]) =
  case unify left right of
    Just unifier ->
      Clause
        (apply unifier headTerm)
        (map (apply unifier) rhs)
    Nothing -> error "Inlining equality should always be unifiable."
inlinedClause _ _ = error "Inlining term should be an equality."
