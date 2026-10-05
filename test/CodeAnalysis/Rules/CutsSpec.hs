module CodeAnalysis.Rules.CutsSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  AdditionalMessage (AdditionalMessage),
  CodeAnalysisConfig (..),
  CutUsageConfig (..),
  Severity (..),
  WithSeverity (..),
 )
import Test.Hspec (Spec, describe, it)

caConfig :: Maybe String -> CodeAnalysisConfig
caConfig cMsg =
  emptyCodeAnalysisConfig {
    cutUsage =
      CutUsageConfig $ Just $ WithSeverity Error $ AdditionalMessage cMsg
    }

hasCut :: [String]
hasCut =
  [ "p(X) :- q(X), !."
  , "p(X) :- a(X), (b(X), ! ; c(X))."
  ]

errorFree :: [String]
errorFree =
  [ "p(X,Y) :- q(X,Y)."
  ]

spec :: Spec
spec = describe "NoSingletonVariables" $ do
  describe "Should detect usage of cut" $
    forM_ hasCut $ \programCode ->
      it programCode $
        shouldDetectProblemsStrict
          (caConfig Nothing)
          [isInfixOf "makes use of the cut (!) operator"]
          programCode
  describe "Should not detect any problems" $
    forM_ errorFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems
          (caConfig Nothing)
          programCode
  it "should provide additional message when configured" $
    shouldDetectProblemsStrict
      (caConfig $ Just "We have not introduced this operator yet.")
      [isInfixOf "We have not introduced this operator yet."]
      "p(X) :- q(X), !."
