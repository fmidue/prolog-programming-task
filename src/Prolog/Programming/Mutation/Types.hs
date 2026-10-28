{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Prolog.Programming.Mutation.Types (
  Mutator,
  Mutation (..),
  MutantStatus (..),
  MutantState (..),
) where

import Data.Data (Data, Proxy)
import GHC.Generics (Generic)
import Language.Prolog (Atom, Goal, Term)

type Mutator = [(Atom, [Term], [Goal])] -> [MutantState Proxy]

data Mutation = DropClause (Atom, [Term], [Goal]) | DropGoal (Atom, [Term], [Goal]) Goal
  deriving (Data, Eq, Generic, Show)

data MutantStatus = Dead | Alive
  deriving (Data, Eq, Generic, Show)

data MutantState m = MutantState {
  mutatedProgram :: [(Atom, [Term], [Goal])]
  , mutation :: Mutation
  , mutantStatus :: m MutantStatus
  }
