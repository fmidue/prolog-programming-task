module Prolog.Programming.Mutation (runMutations, filterAliveMutants) where

import Control.Monad (forM)
import Control.Monad.Identity (Identity (..), runIdentity)
import Language.Prolog (Atom, Goal, Term)
import Prolog.Programming.Mutation.Types (MutantState (..), MutantStatus (..), Mutator)

runMutations
  :: Mutator
  -> ([(Atom, [Term], [Goal])] -> IO Bool)
  -> [(Atom, [Term], [Goal])]
  -> IO [MutantState Identity]
runMutations mutator check prog = do
  let mutants = mutator prog

  forM mutants $ \(MutantState mp m _) -> do
    res <- check mp
    pure $ MutantState mp m $ Identity $ if res then Alive else Dead

filterAliveMutants :: [MutantState Identity] -> [MutantState Identity]
filterAliveMutants = filter ((== Alive) . runIdentity . mutantStatus)
