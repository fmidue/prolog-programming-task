module Prolog.Programming.Mutation (runMutations, filterAliveMutants) where

import Control.Monad (forM)
import Language.Prolog (ProgramClause)
import Prolog.Programming.Mutation.Types (MutantState (..), MutantStatus (..))

runMutations
  :: ([ProgramClause] -> IO Bool)
  -> [MutantState]
  -> IO [(MutantState, MutantStatus)]
runMutations check mutants = do
  forM mutants $ \(MutantState mp m) -> do
    res <- check mp
    pure (MutantState mp m, if res then Alive else Dead)

filterAliveMutants :: [(MutantState, MutantStatus)] -> [(MutantState, MutantStatus)]
filterAliveMutants = filter ((== Alive) . snd)
