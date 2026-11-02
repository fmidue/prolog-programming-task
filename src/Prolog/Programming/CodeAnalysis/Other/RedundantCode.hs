module Prolog.Programming.CodeAnalysis.Other.RedundantCode (
  checkForRedundantCode,
) where

import Data.Maybe (listToMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), ProgramClause, prettifyClause, prettifyTerm)
import Prolog.Programming.CodeAnalysis.Types (
  Problem (..),
  RedundantCodeConfig (..),
  WithSeverity (WithSeverity),
 )
import Prolog.Programming.Mutation (runMutationsAndFilterAlive)
import Prolog.Programming.Mutation.Mutators (dropClauseMutator, dropGoalMutator)
import Prolog.Programming.Mutation.Types (Mutation (..))
import Text.PrettyPrint.Leijen.Text (indent, text, vsep)

checkForRedundantCode
  :: RedundantCodeConfig
  -> ([ProgramClause] -> IO Bool)
  -> [ProgramClause]
  -> IO (Maybe (WithSeverity Problem))
checkForRedundantCode (RedundantCodeConfig Nothing) _ _ = pure Nothing
checkForRedundantCode (RedundantCodeConfig (Just (WithSeverity severity ()))) checker prog = do
  let toResult = pure . fmap (WithSeverity severity . toProblem)
  dropClausesResult <- listToMaybe <$> runMutationsAndFilterAlive checker (dropClauseMutator prog)
  case dropClausesResult of
    Just _ -> toResult dropClausesResult
    Nothing -> do
      dropGoalsResult <- listToMaybe <$> runMutationsAndFilterAlive checker (dropGoalMutator prog)
      toResult dropGoalsResult

toProblem :: Mutation -> Problem
toProblem = Problem . displaySuggestion
  where
    displaySuggestion (DropClause (n, a, g)) =
      vsep
        [ text $ pack "The clause"
        , indent 2 $ text $ pack $ prettifyClause $ Clause n a g
        , text $ pack "is redundant and can be removed."
        ]
    displaySuggestion (DropGoal (n, a, g) goal) =
      vsep
        [ text $ pack "The goal"
        , indent 2 $ text $ pack $ prettifyTerm goal
        , text $ pack "in clause"
        , indent 2 $ text $ pack $ prettifyClause $ Clause n a g
        , text $ pack "is redundant and can be removed."
        ]
