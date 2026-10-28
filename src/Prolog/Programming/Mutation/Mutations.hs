module Prolog.Programming.Mutation.Mutations where

import Data.Bifunctor (first)
import Data.Data (Proxy (..))
import Data.List.Extra (notNull)
import Prolog.Programming.Mutation.Types (MutantState (..), Mutation (..), Mutator)

{- | Returns a list of all subsequences with exactly one element removed.
The list contains tuples consisting of the removed element and the remaining list.
-}
subsequencesWithOneRemoved :: [a] -> [(a, [a])]
subsequencesWithOneRemoved [] = []
subsequencesWithOneRemoved list = go list id
  where
    go [] _ = []
    go (x : xs) addPrefix = (x, addPrefix xs) : res
      where
        res = go xs (addPrefix . (x :))

-- | Returns all possible programs where one clause is dropped
dropClauseMutator :: Mutator
dropClauseMutator =
  map
    (\(dropped, newProg) -> MutantState newProg (DropClause dropped) Proxy)
    . filter (notNull . snd)
    . subsequencesWithOneRemoved

-- | Returns all possible programs where exactly one goal is dropped
dropGoalMutator :: Mutator
dropGoalMutator prog = go prog id
  where
    go [] _ = []
    go (c@(n, a, g) : cs) addPrefix =
      [MutantState (addPrefix $ (n, a, goals) : cs) what Proxy | (what, goals) <- dropGoal g] ++ res
      where
        res = go cs (addPrefix . (c :))

        dropGoal = map (first (DropGoal c)) . subsequencesWithOneRemoved
