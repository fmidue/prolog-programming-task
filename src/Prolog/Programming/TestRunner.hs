module Prolog.Programming.TestRunner (
  testRunner,
  TestResult(..),
  TestSuiteResult(..),
  AreAllOk(..),
  AbortReason(..),
  ) where

import Prolog.Programming.Helper        (termHead)
import Prolog.Programming.TestSpec

import Control.Exception                (evaluate)
import Control.Monad.Random.Class       (MonadRandom)

import Data.List                        (nub, (\\))
import Data.List.NonEmpty               (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty (reverse)
import Data.Maybe                       (isNothing, fromMaybe)

import Language.Prolog                  (Unifier, Goal, Term (Struct), Program, apply, Atom, Clause(..))
import Language.Prolog.GraphViz         (Graph, resolveFirstTree, resolveTree)

import System.Random.Shuffle            (shuffleM)
import System.Timeout                   (timeout)

testRunner :: TimeoutDuration
  -> Program
  -> Program
  -> [Spec]
  -> [(Term, Atom, String)]
  -> IO (TestSuiteResult Spec [Unifier], (Int, Int))
testRunner globalTO factProg inputProg specs newDefs = do
  let
    newProg = useFoundDefsInProgram newDefs factProg
    newSpecs = useFoundDefsInSpecs newDefs specs
    p = newProg ++ inputProg

  testCases <- reorderTests newSpecs
  runTests testCases (checkWithTimeout p)
  where
    checkWithTimeout p s@(Spec _ _ _ to _) = do
      res <- case to of
        GlobalTimeout -> do
          timeout (mili2microSec globalTO) $ evaluate (checkProgram p s)
        LocalTimeout d -> do
          timeout (mili2microSec d) $ evaluate (checkProgram p s)
      pure $ fromMaybe Timeout res
    mili2microSec = (* 1000)

useFoundDefsInProgram :: [(Term,Atom,String)] -> [Clause] -> [Clause]
useFoundDefsInProgram ds clauses = updateClause <$> clauses
  where
    replace = replaceHeads ds
    updateClause :: Clause -> Clause
    updateClause (Clause hd gs) = Clause (replace hd) (map replace gs)
    updateClause (ClauseFn hd f) = ClauseFn (replace hd) (map replace . f)

useFoundDefsInSpecs :: [(Term,Atom,String)] -> [Spec] -> [Spec]
useFoundDefsInSpecs ds specs = updateSpec <$> specs
  where
    replace = replaceHeads ds
    updateSpec :: Spec -> Spec
    updateSpec (Spec v t e to r) = Spec v t e to (updateReq r)
    updateReq :: Requirement -> Requirement
    updateReq (NewPredDecl t d) =
      NewPredDecl t d
    updateReq (QueryWithAnswers ts tss) =
      QueryWithAnswers (replace <$> ts) (map (map replace) tss)
    updateReq (StatementToCheck ts) =
      StatementToCheck $ replace <$> ts

replaceHeads :: [(Term, Atom, c)] -> Term -> Term
replaceHeads ds = replaceHead
  where
    substitutions = map (\(tl,tr,_) -> (fst $ termHead tl,tr)) ds
    replaceHead :: Term -> Term
    replaceHead (Struct h ts) =
      case lookup h substitutions of
        Just r -> Struct r (replaceHead <$> ts)
        Nothing -> Struct h (replaceHead <$> ts)
    replaceHead t = t

data TestResult res
  = Ok
  | Wrong (Maybe Graph) res
  | ErrorMsg String
  | Timeout

data TestSuiteResult a res
  = Finished (AreAllOk a)
  | Aborted (AbortReason a res)

data AreAllOk a
  = AllOk
  | SomeTimeouts (NonEmpty a)

data AbortReason a res
  = OnWrong a (Maybe Graph) res
  | OnErrorMsg a String

{- |
run a sequence of tests until the first error
returns the result and the test that produced the error
additionally the number of passed tests and tests that were not run is returned
(timeout are not counted as errors unless no other error occurs)
-}
runTests
  :: Monad m
  => [a]
  -> (a -> m (TestResult r))
  -> m (TestSuiteResult a r, (Int,Int))
runTests = runTests' 0 []
  where
    runTests' n [] [] _ = pure (Finished AllOk, (n,0))
    runTests' n (t:ts) [] _ = pure (Finished $ SomeTimeouts (NonEmpty.reverse (t :| ts)), (n,0))
    runTests' n ts (x:xs) check = do
      res <- check x
      case res of
        Ok -> runTests' (n+1) ts xs check
        Wrong g r -> pure (Aborted $ OnWrong x g r, (n,length xs))
        ErrorMsg msg -> pure (Aborted $ OnErrorMsg x msg, (n,length xs))
        Timeout -> runTests' n (x:ts) xs check

checkProgram :: Program -> Spec -> TestResult [Unifier]
checkProgram p (Spec _ t r _ (QueryWithAnswers query expected)) =
  case solutions p query of
    Right (actual,_)
      | expect r (applySolutions actual query =~= expected)
      -> Ok
    Right (actual, tree)
      -> Wrong (treeValue t tree) actual
    Left err
      -> ErrorMsg err
checkProgram p (Spec _ t r _ (StatementToCheck query)) =
  case firstSolution p query of
    Right (actual,tree)
      | expect r (isNothing actual)
      -> Wrong (treeValue t tree) (maybe [] pure actual)
    Right _
      -> Ok
    Left err
      -> ErrorMsg err
checkProgram _ (Spec _ _ _ _ NewPredDecl{}) = Ok -- test are already insterted elsewhere

expect :: Expection -> Bool -> Bool
expect PositiveResult = id
expect NegativeResult = not

treeValue :: Visualize -> a -> Maybe a
treeValue DontShowTree _ = Nothing
treeValue ShowTree t = Just t

(=~=) :: [[Term]] -> [[Term]] -> Bool
actual =~= expected =
  nub actual `isSublistOf` nub expected
  && nub expected `isSublistOf` nub actual
  where
    isSublistOf xs ys = null (xs \\ ys)

solutions :: Program -> [Goal] -> Either String ([Unifier], Graph)
solutions = resolveTree

firstSolution :: Program -> [Goal] -> Either String (Maybe Unifier, Graph)
firstSolution = resolveFirstTree

applySolutions :: [Unifier] -> [Goal] -> [[Term]]
applySolutions xs q = map (\s -> map (apply s) q) xs

reorderTests :: MonadRandom m => [Spec] -> m [Spec]
reorderTests = shuffleConcat . classify
  where
    shuffleConcat
      :: MonadRandom m
      => (([Spec],[Spec],[Spec],[Spec],[Spec]),[Spec])
      -> m [Spec]
    shuffleConcat ((xs1,xs2,xs3,xs4,xs5),xs6) = do
      ys1 <- shuffleM xs1
      ys2 <- shuffleM xs2
      ys3 <- shuffleM xs3
      ys4 <- shuffleM xs4
      ys5 <- shuffleM xs5
      ys6 <- shuffleM xs6
      pure $ ys1 ++ ys2 ++ ys3 ++ ys4 ++ ys5 ++ ys6
    -- there is no Monoid instance for 6-tuples for some reason,
    -- so we use nested tuples instead
    -- results in a tuple (non-hidden, hidden)
    -- with non-hiden =
    -- (positiveWithTree,negativeWithTree,positiveNoTree,negativeNoTree,queries)
    classify :: [Spec] -> (([Spec],[Spec],[Spec],[Spec],[Spec]),[Spec])
    classify = mconcat . map classify'
    classify' :: Spec -> (([Spec],[Spec],[Spec],[Spec],[Spec]),[Spec])
    classify' s@(Spec (Hidden _) _ _ _ _)
      = (([],[],[],[],[]),[s])
    classify' s@(Spec Visible _ _ _ QueryWithAnswers{})
      = (([],[],[],[],[s]),[])
    classify' s@(Spec Visible DontShowTree NegativeResult _ _)
      = (([],[],[],[s],[]),[])
    classify' s@(Spec Visible DontShowTree PositiveResult _ _)
      = (([],[],[s],[],[]),[])
    classify' s@(Spec Visible ShowTree NegativeResult _ _)
      = (([],[s],[],[],[]),[])
    classify' s@(Spec Visible ShowTree PositiveResult _ _)
      = (([s],[],[],[],[]),[])
