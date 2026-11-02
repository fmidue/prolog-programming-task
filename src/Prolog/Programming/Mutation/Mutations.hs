module Prolog.Programming.Mutation.Mutations (
  dropClauseMutator,
  dropGoalMutator,
) where

import Data.Bifunctor (first)
import Data.List.Extra (notNull)
import Data.List.HT (removeEach)
import Prolog.Programming.Mutation.Types (MutantState (..), Mutation (..), Mutator)

-- | Returns all possible programs where one clause is dropped
dropClauseMutator :: Mutator
dropClauseMutator =
  map
    (\(dropped, newProg) -> MutantState newProg (DropClause dropped))
    . filter (notNull . snd)
    . removeEach

-- | Returns all possible programs where exactly one goal is dropped
dropGoalMutator :: Mutator
dropGoalMutator prog = go prog id
  where
    go [] _ = []
    go (c@(n, a, g) : cs) addPrefix =
      [MutantState (addPrefix $ (n, a, goals) : cs) what | (what, goals) <- dropGoal g] ++ res
      where
        res = go cs (addPrefix . (c :))

        dropGoal = map (first (DropGoal c)) . removeEach
