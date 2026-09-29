module CodeAnalysis.Rules.MixedSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Types (
  AdditionalMessage (..),
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  ConsistentArityConfig (..),
  CutUsageConfig (..),
  Severity (..),
  SingletonVariablesConfig (..),
 )
import Test.Hspec (Expectation, Spec, describe, it)

caConfig :: CodeAnalysisConfig
caConfig =
  CodeAnalysisConfig {
    singletonVariables =
      SingletonVariablesConfig $ Detect Hint ()
    , cutUsage =
        CutUsageConfig $ Detect Error $ AdditionalMessage Nothing
    , consistentArity = ConsistentArityConfig Ignore
    }

detectsProblems :: String -> Expectation
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
