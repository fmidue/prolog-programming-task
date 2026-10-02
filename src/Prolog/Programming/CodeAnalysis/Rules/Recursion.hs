module Prolog.Programming.CodeAnalysis.Rules.Recursion (recursionChecker) where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (intercalate, sort)
import qualified Data.Map as Map (fromListWith, toList)
import qualified Data.Set as Set (toList, union)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause)
import Prolog.Programming.CodeAnalysis.Helper (clauseIdentities)
import Prolog.Programming.CodeAnalysis.Types (
  AdditionalMessage (..),
  Predicate,
  Problem (..),
  ProgramRule,
 )
import Text.PrettyPrint.Leijen.Text (empty, indent, string, vsep)

recursionChecker :: AdditionalMessage -> ProgramRule
recursionChecker (AdditionalMessage cMsg) clauses = map (toProblem cMsg) foundCycles
  where
    foundCycles = [c | CyclicSCC c <- stronglyConnComp $ buildGraph clauses]

buildGraph :: [Clause] -> [(Predicate, Predicate, [Predicate])]
buildGraph clauses =
  [ (predicate, predicate, Set.toList calls)
  | (predicate, calls) <-
      Map.toList
        $ Map.fromListWith Set.union
        $ map clauseIdentities clauses
  ]

toProblem :: Maybe String -> [Predicate] -> Problem
toProblem cMsg recursivePredicates =
  Problem {
    problemDisplay =
      vsep
        [ string $ pack "Your code contains code that potentially makes use of recursion."
        , string $ pack $ recursionDescription names
        , indent 2 $ string $ pack $ intercalate ", " names
        , maybe empty (string . pack) cMsg
        ]
    }
  where
    names = sort $ map (\(n, a) -> n ++ "/" ++ show a) recursivePredicates

    recursionDescription [_] = "The self-recursive predicate is:"
    recursionDescription _ = "The mutually recursive predicates are:"
