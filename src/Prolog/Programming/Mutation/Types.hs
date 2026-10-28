module Prolog.Programming.Mutation.Types (
  Mutator,
  Mutation (..),
  MutantStatus (..),
  MutantState (..),
) where

import Data.Data (Proxy)
import Language.Prolog (Atom, Goal, Term)

type Mutator = [(Atom, [Term], [Goal])] -> [MutantState Proxy]

data Mutation = DropClause (Atom, [Term], [Goal]) | DropGoal (Atom, [Term], [Goal]) Goal

data MutantStatus = Dead | Alive
  deriving Eq

data MutantState m = MutantState {
  mutatedProgram :: [(Atom, [Term], [Goal])]
  , mutation :: Mutation
  , mutantStatus :: m MutantStatus
  }
