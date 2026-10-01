module Prolog.Programming.CodeAnalysis.Rules.Recursion (recursionChecker) where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (intercalate, sort)
import qualified Data.Map as Map (fromListWith, toList)
import Data.Set (Set)
import qualified Data.Set as Set (empty, fromList, toList, union)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (
  AdditionalMessage (..),
  Problem (..),
  ProgramRule,
 )
import Text.PrettyPrint.Leijen.Text (empty, indent, string, vsep)

recursionChecker :: AdditionalMessage -> ProgramRule
recursionChecker (AdditionalMessage cMsg) clauses = map (toProblem cMsg) foundCycles
  where
    foundCycles = [c | CyclicSCC c <- stronglyConnComp $ buildGraph clauses]

type Predicate = (String, Int)

buildGraph :: [Clause] -> [(Predicate, Predicate, [Predicate])]
buildGraph clauses =
  [ (predicate, predicate, Set.toList calls)
  | (predicate, calls) <-
      Map.toList
        $ Map.fromListWith Set.union
        $ map (\c -> (head $ grabIdentity $ lhs c, clauseEdges c)) clauses
  ]

clauseEdges :: Clause -> Set Predicate
clauseEdges (Clause _ rhs) = Set.fromList $ concatMap grabIdentity rhs
clauseEdges _ = Set.empty

grabIdentity :: Term -> [Predicate]
grabIdentity (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      concatMap grabIdentity args
  | otherwise = [(name, length args)]
grabIdentity _ = []

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
