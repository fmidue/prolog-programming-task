module Prolog.Programming.Mutation (findFirstAliveMutation) where

import Control.Monad.Extra (firstJustM)
import Language.Prolog (ProgramClause)
import Prolog.Programming.Mutation.Types (Mutant (..), Mutation)

findFirstAliveMutation
  :: ([ProgramClause] -> IO Bool)
  -> [Mutant]
  -> IO (Maybe Mutation)
findFirstAliveMutation check = firstJustM $ \(Mutant mp m) -> do
  res <- check mp
  case res of
    False -> pure Nothing
    True -> pure $ Just m
