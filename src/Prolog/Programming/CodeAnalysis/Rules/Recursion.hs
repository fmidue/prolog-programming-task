module Prolog.Programming.CodeAnalysis.Rules.Recursion (recursionChecker) where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (intercalate, sort)
import Data.List.Extra (groupSort, nubOrd)
import Data.Maybe (mapMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (indent, string, vsep)

recursionChecker :: ProgramRule
recursionChecker clauses = map toProblem foundCycles
  where
    foundCycles = cycles $ buildGraph clauses

type Predicate = (String, Int)

buildGraph :: [Clause] -> [(Predicate, Predicate, [Predicate])]
buildGraph clauses =
  [ (predicate, predicate, nubOrd $ concat calls)
  | (predicate, calls) <- groupSort $ mapMaybe clauseEdges clauses
  ]

clauseEdges :: Clause -> Maybe (Predicate, [Predicate])
clauseEdges (Clause (Struct name args) rhs) =
  Just ((name, length args), concatMap grabIdentity rhs)
clauseEdges _ = Nothing

grabIdentity :: Term -> [Predicate]
grabIdentity (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      concatMap grabIdentity args
  | otherwise = [(name, length args)]
grabIdentity _ = []

cycles :: [(Predicate, Predicate, [Predicate])] -> [[Predicate]]
cycles graph = [c | CyclicSCC c <- stronglyConnComp graph]

toProblem :: [Predicate] -> Problem
toProblem recursivePredicates =
  Problem {
    problemDisplay =
      vsep
        [ string $ pack "Your code contains code that potentially makes use of recursion."
        , string $ pack $ recursionDescription names
        , indent 2 $ string $ pack $ intercalate ", " names
        ]
    }
  where
    names = sort $ map (\(n, a) -> n ++ "/" ++ show a) recursivePredicates

    recursionDescription [_] = "The self-recursive predicate is:"
    recursionDescription _ = "The mutually recursive predicates are:"
