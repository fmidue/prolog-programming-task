{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}

module CodeAnalysis.MutationSpec where

import Test.Hspec (Spec, describe, it, shouldSatisfy)

import Data.IORef (modifyIORef, newIORef, readIORef)
import Data.List (isInfixOf, isPrefixOf)
import Prolog.Programming.Task (checkTask, toInstance)
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

spec :: Spec
spec = describe "Mutation" $ do
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

      reportRef <- newIORef []

      () <- checkTask (fail . show) (\doc -> modifyIORef reportRef (show doc :)) (const $ pure ()) config code
      report <- readIORef reportRef

      report `shouldSatisfy` any (\p -> "The goal" `isInfixOf` p && "A =:= B" `isInfixOf` p)
    it "detects redundant length([],0) clause" $ do
      let code =
            [RS.r|
length([],0).
length([X|Xs],L) :- length(Xs,R), L is R + 1.

check([],[]).
check([X|Xs],[Y|Ys]) :- Y is X * 2, check(Xs,Ys).
      |]

      reportRef <- newIORef []

      () <- checkTask (fail . show) (\doc -> modifyIORef reportRef (show doc :)) (const $ pure ()) config code
      report <- readIORef reportRef

      report `shouldSatisfy` any (\p -> "The clause" `isInfixOf` p && "length([], 0)." `isInfixOf` p)
    it "detects redundant task definitions in submission when includeTaskDefinition is set to 'yes'" $ do
      {- Task definitions that are included in the submission may be marked as redundant iff includeTaskDefinition is set to 'yes'.
        With includeTaskDefinition set to 'filtered' or 'no', the included definition will not be part of the background facts.
        Dropping the definition will then lead to test failures indicating that the definition is not redundant.
      -}
      let code =
            [RS.r|
check([],[]).
check([X|Xs],[Y|Ys]) :- Y is X * 2, check(Xs,Ys).
      |]

      reportRef <- newIORef []

      let config' = toInstance $ "includeTaskDefinitions: yes\n" ++ taskConfig
      () <- checkTask (fail . show) (\doc -> modifyIORef reportRef (show doc :)) (const $ pure ()) config' code
      report <- readIORef reportRef

      report `shouldSatisfy` any (\p -> "The clause" `isInfixOf` p && "check([], [])." `isInfixOf` p)
    it "does not detect redundant task definitions in submission when includeTaskDefinition is set to 'filtered'" $ do
      let code =
            [RS.r|
check([],[]).
check([X|Xs],[Y|Ys]) :- Y is X * 2, check(Xs,Ys).
      |]

      reportRef <- newIORef []

      () <- checkTask (fail . show) (\doc -> modifyIORef reportRef (show doc :)) (const $ pure ()) config code
      report <- readIORef reportRef

      report `shouldSatisfy` \case
        [r] -> "Ok" `isPrefixOf` r
        _ -> False
    it "does not detect redundant task definitions in submission when includeTaskDefinition is set to 'no'" $ do
      let code =
            [RS.r|
check([],[]).
check([X|Xs],[Y|Ys]) :- Y is X * 2, check(Xs,Ys).
      |]

      reportRef <- newIORef []

      let config' = toInstance $ "includeTaskDefinitions: no\n" ++ taskConfig
      () <- checkTask (fail . show) (\doc -> modifyIORef reportRef (show doc :)) (const $ pure ()) config' code
      report <- readIORef reportRef

      report `shouldSatisfy` \case
        [r] -> "Ok" `isPrefixOf` r
        _ -> False
