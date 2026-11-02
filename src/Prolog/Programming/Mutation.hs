module Prolog.Programming.Mutation (runMutationsAndFilterAlive) where

import Control.Monad (forM)
import Data.Maybe (catMaybes)
import Language.Prolog (ProgramClause)
import Prolog.Programming.Mutation.Types (MutantState (..), Mutation)

runMutationsAndFilterAlive
  :: ([ProgramClause] -> IO Bool)
  -> [MutantState]
  -> IO [Mutation]
runMutationsAndFilterAlive check mutants = do
  processed <- forM mutants $ \(MutantState mp m) -> do
    res <- check mp
    case res of
      False -> pure Nothing
      True -> pure $ Just m

  pure $ catMaybes processed
