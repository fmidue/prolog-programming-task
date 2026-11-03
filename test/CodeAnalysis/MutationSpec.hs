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
/* Define a predicate check/2 that checks if the second list
 * is the first list with every list item multiplied by two.
 */
------------------------------
check([],[]).
check([X|Xs],[Y|Ys]) :- Y is X * 2, check(Xs,Ys).
|]

spec :: Spec
spec = describe "Mutation" $ do
  describe "tests on an actual task" $ do
    let config = toInstance taskConfig
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
    it "detects no redundant goal or clause" $ do
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
