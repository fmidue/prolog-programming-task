{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}

module CodeAnalysis.MutationSpec where

import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Control.Exception (IOException, try)
import Data.IORef (modifyIORef, newIORef, readIORef)
import Data.List (isInfixOf, isPrefixOf)
import Language.Prolog (Atom, Term (..), consultString)
import Prolog.Programming.Mutation.Mutators (dropGoalMutator)
import Prolog.Programming.Mutation.Types (Mutant (..), Mutation (..))
import Prolog.Programming.Task (TaskInstance, checkTask, toInstance)
import Test.HUnit (assertFailure)
import qualified Text.RawString.QQ as RS (r)

taskConfig :: String
taskConfig =
  [RS.r|
codeAnalysis:
  redundantCode:
    status: hint

specifications:
 - 'check([],[])'
 - '-check([1],[])'
 - '-check([],[1])'
 - 'check([0],[0])'
 - '!check([1,2,3],[2,4,6])'
 - '-!check([1,2,3],[6,4,2])'
 - '-!check([1,2,3],[2,2,3])'
------------------------------
/* Complete the definition for the predicate check/2 that checks if
 * the second list is the first list with every list item
 * multiplied by two.
 */
check([],[]).
------------------------------
check([X|Xs],[Y|Ys]) :- Y is X * 2, check(Xs,Ys).
|]

constant :: Atom -> Term
constant name = Struct name []

con :: Term -> Term -> Term
con l r = Struct "," [l, r]

dis :: Term -> Term -> Term
dis l r = Struct ";" [l, r]

evaluateCheck :: TaskInstance -> String -> IO [String]
evaluateCheck inst code = case consultString code of
  Left err -> assertFailure $ "failed to parse program" ++ show err
  Right inProg -> do
    ref <- newIORef id

    let updateInform doc = modifyIORef ref (\is -> is . (show doc :))

    _ <- try (checkTask (fail . show) updateInform (const $ pure ()) inst inProg) :: IO (Either IOException ())

    infos <- readIORef ref

    pure $ infos []

spec :: Spec
spec = describe "Mutation" $ do
  describe "dropGoalMutator" $ do
    it "removes one non-connective goal from deeply nested conjunctions and disjunctions" $ do
      let outcomes =
            [ (deleted, goals)
            | Mutant [(_, _, goals)] (DropGoal _ deleted) <-
                dropGoalMutator
                  [("p", [], [dis (con (constant "a") (dis (constant "b") (constant "c"))) (constant "f")])]
            ]

      outcomes
        `shouldBe` [ (constant "a", [dis (dis (constant "b") (constant "c")) (constant "f")])
                   , (constant "b", [dis (con (constant "a") (constant "c")) (constant "f")])
                   , (constant "c", [dis (con (constant "a") (constant "b")) (constant "f")])
                   , (constant "f", [con (constant "a") (dis (constant "b") (constant "c"))])
                   ]
  describe "tests on an actual task" $ do
    let config = toInstance $ "includeTaskDefinitions: filtered\n" ++ taskConfig
    it "detects redundant A =:= B goal" $ do
      let code =
            [RS.r|
length([],0).
length([X|Xs],L) :- length(Xs,R), L is R + 1.

check([],[]).
check([X|Xs],[Y|Ys]) :- Y is X * 2, length(Xs,A), length(Ys,B), A =:= B, check(Xs,Ys).
      |]

      report <- evaluateCheck config code

      report `shouldSatisfy` any (\p -> "One literal" `isInfixOf` p && "A =:= B" `isInfixOf` p)
    it "detects redundant length([],0) clause" $ do
      let code =
            [RS.r|
length([],0).
length([X|Xs],L) :- length(Xs,R), L is R + 1.

check([],[]).
check([X|Xs],[Y|Ys]) :- Y is X * 2, check(Xs,Ys).
      |]

      report <- evaluateCheck config code

      report `shouldSatisfy` any (\p -> "The clause" `isInfixOf` p && "length([], 0)." `isInfixOf` p)
    it "detects redundant task definitions in submission when includeTaskDefinition is set to 'yes'" $ do
      {-
        Task definitions that are included in the submission may be marked as redundant
        iff includeTaskDefinition is set to 'yes'. With includeTaskDefinition set to 'filtered'
        or 'no', the included definition will not be part of the background facts. Dropping the
        definition will then lead to test failures indicating that the definition is not redundant.
      -}
      let code =
            [RS.r|
check([],[]).
check([X|Xs],[Y|Ys]) :- Y is X * 2, check(Xs,Ys).
      |]

      let config' = toInstance $ "includeTaskDefinitions: yes\n" ++ taskConfig
      report <- evaluateCheck config' code

      report `shouldSatisfy` any (\p -> "The clause" `isInfixOf` p && "check([], [])." `isInfixOf` p)
    it "does not detect redundant task definitions in submission when includeTaskDefinition is set to 'filtered'" $ do
      let code =
            [RS.r|
check([],[]).
check([X|Xs],[Y|Ys]) :- Y is X * 2, check(Xs,Ys).
      |]

      report <- evaluateCheck config code

      report `shouldSatisfy` \case
        [r] -> "Ok" `isPrefixOf` r
        _ -> False
    it "does not detect redundant task definitions in submission when includeTaskDefinition is set to 'no'" $ do
      let code =
            [RS.r|
check([],[]).
check([X|Xs],[Y|Ys]) :- Y is X * 2, check(Xs,Ys).
      |]

      let config' = toInstance $ "includeTaskDefinitions: no\n" ++ taskConfig
      report <- evaluateCheck config' code

      report `shouldSatisfy` \case
        [r] -> "Ok" `isPrefixOf` r
        _ -> False
