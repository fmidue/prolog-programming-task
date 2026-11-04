module CodeAnalysis.CheckStageSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict', shouldNotHaveProblems')
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CheckStage (AfterTests, BeforeTests),
  CodeAnalysisConfig (..),
  Severity (..),
  SingletonVariablesConfig (..),
  WithSeverity (..),
 )
import Test.Hspec (Spec, describe, it)

caConfig :: CodeAnalysisConfig
caConfig =
  emptyCodeAnalysisConfig {
    singletonVariables =
      SingletonVariablesConfig $ Just (WithSeverity Hint (), AfterTests)
    }

spec :: Spec
spec = describe "Check stages work" $ do
  it "should apply checker at the specified staged" $
    shouldDetectProblemsStrict'
      AfterTests
      caConfig
      [ isInfixOf "includes the singleton variable"
      ]
      "a(X)."
      ""
  it "should not apply checker when in other stage" $
    shouldNotHaveProblems'
      BeforeTests
      caConfig
      "a(X)."
      ""
