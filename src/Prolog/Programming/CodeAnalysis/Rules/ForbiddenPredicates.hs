{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.ForbiddenPredicates (forbiddenPredicatesChecker) where

import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as Set (intersection, toList)
import Data.Text.Lazy (pack)
import Language.Prolog (Atom, Clause (..), Goal, Term)
import Prolog.Programming.CodeAnalysis.Helper (clauseIdentities)
import Prolog.Programming.CodeAnalysis.Types (ClauseRule, Predicate, Problem (..))
import Text.PrettyPrint.Leijen.Text (empty, indent, string, vsep)

forbiddenPredicatesChecker :: Set Predicate -> ClauseRule
forbiddenPredicatesChecker forbidden c@(name, args, goals)
  | null usedForbidden = []
  | otherwise = [toProblem Nothing usedForbidden clause]
  where
    clause = Clause name args goals
    usedForbidden = Set.toList $ forbiddenInClause forbidden c

forbiddenInClause :: Set Predicate -> (Atom, [Term], [Goal]) -> Set Predicate
forbiddenInClause forbidden clause = forbidden `Set.intersection` snd (clauseIdentities True clause)

toProblem :: Maybe String -> [Predicate] -> Clause -> Problem
toProblem msg predicates clause =
  Problem {
    problemDisplay =
      vsep
        [ string "Your clause"
        , indent 2 $ string $ pack $ show clause
        , string $ pack $ "makes use of forbidden predicates: " ++ intercalate ", " (map show predicates)
        , maybe empty (string . pack) msg
        ]
    }
