{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.Predicates (predicatesChecker) where

import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as Set (intersection, map, toList)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..))
import Prolog.Programming.CodeAnalysis.Helper (clauseIdentities)
import Prolog.Programming.CodeAnalysis.Types (ClauseRule, ForbiddenPredicate (..), ForbiddenPredicates (..), Predicate, Problem (..))
import Text.PrettyPrint.Leijen.Text (empty, indent, string, vsep)

predicatesChecker :: ForbiddenPredicates -> ClauseRule
predicatesChecker (ForbiddenPredicates forbidden) clause
  | null usedForbidden = []
  | otherwise = [toProblem Nothing usedForbidden clause]
  where
    usedForbidden = Set.toList $ forbiddenInClause forbidden clause

forbiddenInClause :: Set ForbiddenPredicate -> Clause -> Set Predicate
forbiddenInClause forbidden clause = Set.map (\(ForbiddenPredicate p) -> p) forbidden `Set.intersection` snd (clauseIdentities clause)

toProblem :: Maybe String -> [(String, Int)] -> Clause -> Problem
toProblem msg predicates clause =
  Problem {
    problemDisplay =
      vsep
        [ string "Your clause"
        , indent 2 $ string $ pack $ show clause
        , string $ pack $ "makes use of forbidden predicates: " ++ intercalate ", " (map showPredicate predicates)
        , maybe empty (string . pack) msg
        ]
    }
  where
    showPredicate (name, arity) = name ++ "/" ++ show arity
