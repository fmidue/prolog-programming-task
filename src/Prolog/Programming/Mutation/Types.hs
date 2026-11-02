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
import Language.Prolog (Goal, ProgramClause)

type Mutator = [ProgramClause] -> [MutantState Proxy]

data Mutation = DropClause ProgramClause | DropGoal ProgramClause Goal
  deriving (Data, Eq, Generic, Show)

data MutantStatus = Dead | Alive
  deriving (Data, Eq, Generic, Show)

data MutantState m = MutantState {
  mutatedProgram :: [ProgramClause]
  , mutation :: Mutation
  , mutantStatus :: m MutantStatus
  }
