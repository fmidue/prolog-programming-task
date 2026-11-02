module Prolog.Programming.Mutation (testMutantsAndFilterAlive) where

import Control.Monad (forM)
import Data.Maybe (catMaybes)
import Language.Prolog (ProgramClause)
import Prolog.Programming.Mutation.Types (Mutant (..), Mutation)

testMutantsAndFilterAlive
  :: ([ProgramClause] -> IO Bool)
  -> [Mutant]
  -> IO [Mutation]
testMutantsAndFilterAlive check mutants = do
  processed <- forM mutants $ \(Mutant mp m) -> do
    res <- check mp
    case res of
      False -> pure Nothing
      True -> pure $ Just m

  pure $ catMaybes processed
