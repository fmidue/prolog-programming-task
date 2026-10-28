module Prolog.Programming.CodeAnalysis.Other.RedundantCode (
  checkForRedundantCode,
) where

import Control.Monad.Identity (Identity)
import Data.Text.Lazy (pack)
import Language.Prolog (Atom, Clause (..), Goal, Term, prettifyClause, prettifyTerm)
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
  -> ([(Atom, [Term], [Goal])] -> IO Bool)
  -> [(Atom, [Term], [Goal])]
  -> IO [WithSeverity Problem]
checkForRedundantCode (RedundantCodeConfig Nothing) _ _ = pure []
checkForRedundantCode (RedundantCodeConfig (Just (WithSeverity severity _))) checker prog = do
  let toResult = pure . map (WithSeverity severity) . toProblems
  dropClausesResult <- runMutations [dropClauseMutator] checker prog
  case dropClausesResult of
    rs@(_ : _) -> toResult rs
    _ -> do
      dropGoalsResult <- runMutations [dropGoalMutator] checker prog
      toResult dropGoalsResult

toProblems :: [MutantState Identity] -> [Problem]
toProblems = map (Problem . displaySuggestion . mutation) . filterAliveMutants
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
