module Prolog.Programming.Mutation.Mutators (
  dropClauseMutator,
  dropGoalMutator,
) where

import Control.Applicative ((<|>))
import Data.Bifunctor (second)
import Data.List.HT (removeEach)
import Language.Prolog (Atom, Goal, Term (..))
import Prolog.Programming.Mutation.Types (Mutant (..), Mutation (..), Mutator)

-- | Returns all possible programs where one clause is dropped
dropClauseMutator :: Mutator
dropClauseMutator [_] = []
dropClauseMutator prog =
  map
    (\(dropped, newProg) -> Mutant newProg (DropClause dropped))
    $ removeEach prog

-- | Returns all possible programs where exactly one goal is dropped
dropGoalMutator :: Mutator
dropGoalMutator = go id
  where
    go _ [] = []
    go addPrefix (c@(n, a, gs) : cs) =
      [Mutant (addPrefix $ (n, a, goals) : cs) (DropGoal c goal) | (goal, goals) <- removeEachGoal gs]
        ++ go (addPrefix . (c :)) cs

removeEachGoal :: [Goal] -> [(Goal, [Goal])]
removeEachGoal = go id
  where
    go _ [] = []
    go addPrefix (g : gs) =
      map (second (addPrefix . maybe gs (: gs))) (removeAlsoWithinGoal g)
        ++ go (addPrefix . (g :)) gs

    removeAlsoWithinGoal :: Goal -> [(Goal, Maybe Goal)]
    removeAlsoWithinGoal (Struct name [l, r])
      | name `elem` [",", ";"] =
          map (second (flip (combine name) $ Just r)) (removeAlsoWithinGoal l)
            ++ map (second (combine name $ Just l)) (removeAlsoWithinGoal r)
    removeAlsoWithinGoal goal = [(goal, Nothing)]

    combine :: Atom -> Maybe Goal -> Maybe Goal -> Maybe Goal
    combine name (Just l) (Just r) = Just $ Struct name [l, r]
    combine _ l r = l <|> r
