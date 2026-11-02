module Prolog.Programming.Mutation (runMutations, filterAliveMutants) where

import Control.Monad (forM)
import Control.Monad.Identity (Identity (..), runIdentity)
import Data.Data (Proxy)
import Language.Prolog (Atom, Goal, Term)
import Prolog.Programming.Mutation.Types (MutantState (..), MutantStatus (..))

runMutations
  :: ([(Atom, [Term], [Goal])] -> IO Bool)
  -> [MutantState Proxy]
  -> IO [MutantState Identity]
runMutations check mutants = do
  forM mutants $ \(MutantState mp m _) -> do
    res <- check mp
    pure $ MutantState mp m $ Identity $ if res then Alive else Dead

filterAliveMutants :: [MutantState Identity] -> [MutantState Identity]
filterAliveMutants = filter ((== Alive) . runIdentity . mutantStatus)
