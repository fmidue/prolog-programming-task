{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Prolog.Programming.Mutation.Types (
  Mutator,
  Mutation (..),
  Mutant (..),
) where

import Data.Data (Data)
import GHC.Generics (Generic)
import Language.Prolog (Goal, ProgramClause)

type Mutator = [ProgramClause] -> [Mutant]

data Mutation = DropClause ProgramClause | DropGoal ProgramClause Goal
  deriving (Data, Eq, Generic, Show)

data Mutant = Mutant {
  mutatedProgram :: [ProgramClause]
  , mutation :: Mutation
  }
