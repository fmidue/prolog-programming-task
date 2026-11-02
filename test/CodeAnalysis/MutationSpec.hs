{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}

module CodeAnalysis.MutationSpec where

import Prolog.Programming.Mutation (runMutationsAndFilterAlive)
import Prolog.Programming.Mutation.Mutators (dropClauseMutator, dropGoalMutator)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.Maybe (mapMaybe)
import Language.Prolog (Clause (Clause), ProgramClause, Term (..), consultString, prettifyClause, prettifyTerm, var)
import Prolog.Programming.Mutation.Types (Mutation (..))
import qualified Text.RawString.QQ as RS (r)

requirePredicateChecker :: [String] -> [ProgramClause] -> IO Bool
requirePredicateChecker requiredPredicatesNames prog =
  pure $ all (\req -> any (\(n, _, _) -> n == req) prog) requiredPredicatesNames

requireGoalChecker :: [Term] -> [ProgramClause] -> IO Bool
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
        result <- runMutationsAndFilterAlive (requirePredicateChecker ["p"]) $ dropClauseMutator prog

        let droppedClauses = flip mapMaybe result $ \case
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
        result <- runMutationsAndFilterAlive (requireGoalChecker [Struct "b" [var "X"]]) $ dropGoalMutator prog

        let droppedGoalsWithClause = flip mapMaybe result $ \case
              DropGoal (n, a, gs) g -> Just (prettifyTerm g, prettifyClause $ Clause n a gs)
              _ -> Nothing

        droppedGoalsWithClause
          `shouldBe` [ ("a(X)", "p(X) :- a(X), b(X), c(X).")
                     , ("c(X)", "p(X) :- a(X), b(X), c(X).")
                     , ("d(X)", "q(X) :- d(X).")
                     ]
