module Prolog.Programming.Mutation (findFirstAliveMutation) where

import Language.Prolog (ProgramClause)
import Prolog.Programming.Mutation.Types (Mutant (..), Mutation)

findFirstAliveMutation
  :: ([ProgramClause] -> IO Bool)
  -> [Mutant]
  -> IO (Maybe Mutation)
findFirstAliveMutation _ [] = pure Nothing
findFirstAliveMutation check (Mutant mp m : ms) = do
  res <- check mp
  case res of
    False -> findFirstAliveMutation check ms
    True -> pure $ Just m
