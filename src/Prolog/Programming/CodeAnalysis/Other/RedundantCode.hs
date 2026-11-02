module Prolog.Programming.CodeAnalysis.Other.RedundantCode (
  checkForRedundantCode,
) where

import Control.Monad.Identity (Identity)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), ProgramClause, prettifyClause, prettifyTerm)
import Prolog.Programming.CodeAnalysis.Types (
  Problem (..),
  RedundantCodeConfig (..),
  WithSeverity (WithSeverity),
 )
import Prolog.Programming.Mutation (filterAliveMutants, runMutations)
import Prolog.Programming.Mutation.Mutations (dropClauseMutator, dropGoalMutator)
import Prolog.Programming.Mutation.Types (MutantState (..), Mutation (..))
import Text.PrettyPrint.Leijen.Text (indent, text, vsep)

checkForRedundantCode
  :: RedundantCodeConfig
  -> ([ProgramClause] -> IO Bool)
  -> [ProgramClause]
  -> IO (Maybe (WithSeverity Problem))
checkForRedundantCode (RedundantCodeConfig Nothing) _ _ = pure Nothing
checkForRedundantCode (RedundantCodeConfig (Just (WithSeverity severity ()))) checker prog = do
  let toResult = pure . fmap (WithSeverity severity) . toProblems
  dropClausesResult <- runMutations checker $ dropClauseMutator prog
  case dropClausesResult of
    (dc : _) -> toResult [dc]
    _ -> do
      dropGoalsResult <- runMutations checker $ dropGoalMutator prog
      toResult $ take 1 dropGoalsResult

toProblems :: [MutantState Identity] -> Maybe Problem
toProblems ms = case filterAliveMutants ms of
  [] -> Nothing
  (m : _) -> Just $ Problem $ displaySuggestion $ mutation m
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
