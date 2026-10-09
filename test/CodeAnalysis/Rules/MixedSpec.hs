module CodeAnalysis.Rules.MixedSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  AdditionalMessage (..),
  CodeAnalysisConfig (..),
  CutUsageConfig (..),
  Severity (..),
  SingletonVariablesConfig (..),
  WithSeverity (..),
 )
import Prolog.Programming.Data (Code)
import Test.Hspec (Expectation, Spec, describe, it)

caConfig :: CodeAnalysisConfig
caConfig =
  emptyCodeAnalysisConfig {
    singletonVariables =
      SingletonVariablesConfig $ Just $ WithSeverity Hint ()
    , cutUsage =
        CutUsageConfig $ Just $ WithSeverity Error $ AdditionalMessage Nothing
    }

detectsProblems :: Code -> Expectation
detectsProblems =
  shouldDetectProblemsStrict
    caConfig
    [ isInfixOf "includes the singleton variable"
    , isInfixOf "makes use of the cut (!) operator"
    ]

spec :: Spec
spec = describe "Mixed rule tests" $ do
  it "singleton + cut" $
    detectsProblems "a(X) :- X = [Z|Zs], ! , b(Zs)."
