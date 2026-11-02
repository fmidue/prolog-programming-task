{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Prolog.Programming.Mutation.Types (
  Mutator,
  Mutation (..),
  MutantState (..),
) where

import Data.Data (Data)
import GHC.Generics (Generic)
import Language.Prolog (Goal, ProgramClause)

type Mutator = [ProgramClause] -> [MutantState]

data Mutation = DropClause ProgramClause | DropGoal ProgramClause Goal
  deriving (Data, Eq, Generic, Show)

data MutantState = MutantState {
  mutatedProgram :: [ProgramClause]
  , mutation :: Mutation
  }
