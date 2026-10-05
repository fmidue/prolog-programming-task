module CodeAnalysis.Rules.RhsPatternMatchingSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  RhsPatternMatchingConfig (..),
  Severity (..),
  WithSeverity (..),
 )
import Test.Hspec (Spec, describe, it)

caConfig :: CodeAnalysisConfig
caConfig =
  emptyCodeAnalysisConfig {
    rhsPatternMatching =
      RhsPatternMatchingConfig $ Just $ WithSeverity Hint ()
    }

detectsPatternMatches :: [String]
detectsPatternMatches =
  [ "p(Xs,X) :- Xs = [X,_]."
  , "p([X]) :- X = a."
  , "p(X) :- X = leaf."
  , "p(X) :- leaf = X."
  , "p(X) :- X = node(L,V,R), q(V), p(L), p(R)."
  , "p(X) :- X = a, !."
  ]

errorFree :: [String]
errorFree =
  [ "p(Xs,X) :- Xs = [X,_], q(Xs)."
  , "p(X) :- q(X), X = [a]."
  , "p(X) :- !, X = a."
  , "p(X) :- X = [X]."
  , "p(X) :- X =:= a."
  , "p(X) :- q(X)."
  ]

spec :: Spec
spec = describe "RhsPatternMatching" $ do
  describe "Should detect pattern matching on the RHS" $
    forM_ detectsPatternMatches $ \programCode ->
      it programCode $
        shouldDetectProblemsStrict
          caConfig
          [isInfixOf "can be moved to the left-hand side"]
          programCode
  describe "Should not detect unsafe or unrelated equalities" $
    forM_ errorFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems
          caConfig
          programCode
