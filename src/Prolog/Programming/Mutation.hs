module Prolog.Programming.Mutation (runMutationsAndFilterAlive) where

import Control.Monad (forM)
import Data.Maybe (catMaybes)
import Language.Prolog (ProgramClause)
import Prolog.Programming.Mutation.Types (MutantState (..))

runMutationsAndFilterAlive
  :: ([ProgramClause] -> IO Bool)
  -> [MutantState]
  -> IO [MutantState]
runMutationsAndFilterAlive check mutants = do
  processed <- forM mutants $ \(MutantState mp m) -> do
    res <- check mp
    case res of
      False -> pure Nothing
      True -> pure $ Just $ MutantState mp m

  pure $ catMaybes processed
