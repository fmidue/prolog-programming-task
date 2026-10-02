module CodeAnalysis.Rules.ClauseAmountSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  BoundsConfig (BoundsConfig),
  ClauseAmountConfig (ClauseAmountConfig),
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  Severity (..),
 )
import Test.Hspec (Spec, describe, it)

caConfig :: Maybe Int -> Maybe Int -> CodeAnalysisConfig
caConfig lower upper =
  emptyCodeAnalysisConfig {
    clauseAmount =
      ClauseAmountConfig $ Detect Hint $ BoundsConfig lower upper
    }

twoClauses :: String
twoClauses = "p. q."

spec :: Spec
spec = describe "ClauseAmount" $ do
  it "should detect too few clauses" $
    shouldDetectProblemsStrict
      (caConfig (Just 3) Nothing)
      [isInfixOf "Your program has too few clauses."]
      twoClauses
  it "should detect too many clauses" $
    shouldDetectProblemsStrict
      (caConfig Nothing (Just 1))
      [isInfixOf "Your program has too many clauses."]
      twoClauses
  describe "Should not detect any problems at inclusive bounds" $ do
    it "when the clause count equals the lower bound" $
      shouldNotHaveProblems
        (caConfig (Just 2) Nothing)
        twoClauses
    it "when the clause count equals the upper bound" $
      shouldNotHaveProblems
        (caConfig Nothing (Just 2))
        twoClauses
  it "should not detect any problems when no bounds are configured" $
    shouldNotHaveProblems
      (caConfig Nothing Nothing)
      twoClauses
