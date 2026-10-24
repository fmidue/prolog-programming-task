module CodeAnalysis.Rules.EarlyRecursionSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  AdditionalMessage (..),
  CodeAnalysisConfig (..),
  EarlyRecursionConfig (EarlyRecursionConfig),
  Severity (..),
  WithSeverity (..),
 )
import Prolog.Programming.Data (Code)
import Test.Hspec (Spec, describe, it)

caConfig :: CodeAnalysisConfig
caConfig =
  emptyCodeAnalysisConfig {
    earlyRecursion = EarlyRecursionConfig $ Just $ WithSeverity Hint $ AdditionalMessage Nothing
    }

hasViolation :: [Code]
hasViolation =
  [ "p(X) :- p(X), q(X)."
  , "p(X) :- q(X), p(X), r(X)."
  , "p(X) :- p(X), (q(X); r(X))."
  , "p(X) :- p(X), not(q(X))."
  , "p(X) :- (p(X), r(X)), not(q(X))."
  , "p(X) :- (p(X); r(X)), not(q(X))."
  , "p(X) :- p(0), q(X)."
  ]

detectionFree :: [Code]
detectionFree =
  [ "p(X) :- q(X)."
  , "p(X) :- q(X), p(X)."
  , "p(X) :- q(X), (r(X); p(X))."
  , "p(X) :- q(X), not(p(X))."
  , "p(X) :- q(X), (r(X), p(X))."
  , "p(X,Y) :- p(X), p(Y)."
  , "p(s(X)) :- p(0), p(X)."
  ]

spec :: Spec
spec = describe "EarlyRecursion" $ do
  describe "Should detect recursive calls that are not the last goal" $
    forM_ hasViolation $ \programCode ->
      it programCode $
        shouldDetectProblemsStrict
          caConfig
          [isInfixOf "doesn't seem to be a recursive call despite one being used."]
          programCode
  describe "Should not detect recursive calls in the last goal" $
    forM_ detectionFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems caConfig programCode
