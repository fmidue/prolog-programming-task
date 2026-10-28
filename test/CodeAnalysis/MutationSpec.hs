{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}

module CodeAnalysis.MutationSpec where

import Prolog.Programming.Mutation (filterAliveMutants, runMutations)
import Prolog.Programming.Mutation.Mutations (dropClauseMutator, dropGoalMutator)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.Maybe (mapMaybe)
import Language.Prolog (Atom, Clause (Clause), Goal, Term (..), consultString, prettifyClause, prettifyTerm, var)
import Prolog.Programming.Mutation.Types (MutantState (mutation), Mutation (..))
import qualified Text.RawString.QQ as RS (r)

requirePredicateChecker :: [String] -> [(Atom, [Term], [Goal])] -> IO Bool
requirePredicateChecker requiredPredicatesNames prog =
  pure $ all (\req -> any (\(n, _, _) -> n == req) prog) requiredPredicatesNames

requireGoalChecker :: [Term] -> [(Atom, [Term], [Goal])] -> IO Bool
requireGoalChecker requiredGoals prog =
  pure $ all (\req -> any (\(_, _, gs) -> req `elem` gs) prog) requiredGoals

spec :: Spec
spec = describe "Mutation" $ do
  it "reports the all redundant clauses" $ do
    let progDef =
          [RS.r|
p(_).
q(a).
q(X) :- p(X).
    |]

    case consultString progDef of
      Left err -> fail $ show err
      Right prog -> do
        result <- runMutations [dropClauseMutator] (requirePredicateChecker ["p"]) prog

        let droppedClauses = flip mapMaybe (map mutation $ filterAliveMutants result) $ \case
              DropClause (n, a, g) -> Just $ prettifyClause (Clause n a g)
              _ -> Nothing

        droppedClauses `shouldBe` ["q(a).", "q(X) :- p(X)."]
  it "reports the all redundant goals" $ do
    let progDef =
          [RS.r|
p(X) :- a(X), b(X), c(X).
q(X) :- d(X).
    |]

    case consultString progDef of
      Left err -> fail $ show err
      Right prog -> do
        result <- runMutations [dropGoalMutator] (requireGoalChecker [Struct "b" [var "X"]]) prog

        let droppedGoalsWithClause = flip mapMaybe (map mutation $ filterAliveMutants result) $ \case
              DropGoal (n, a, gs) g -> Just (prettifyTerm g, prettifyClause $ Clause n a gs)
              _ -> Nothing

        droppedGoalsWithClause
          `shouldBe` [ ("a(X)", "p(X) :- a(X), b(X), c(X).")
                     , ("c(X)", "p(X) :- a(X), b(X), c(X).")
                     , ("d(X)", "q(X) :- d(X).")
                     ]
