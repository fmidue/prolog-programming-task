module CodeAnalysis.Rules.RecursionSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  AdditionalMessage (AdditionalMessage),
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  RecursionConfig (..),
  Severity (..),
 )
import Test.Hspec (Spec, describe, it)

caConfig :: Maybe String -> CodeAnalysisConfig
caConfig cMsg =
  emptyCodeAnalysisConfig {
    recursion =
      RecursionConfig $ Detect Hint $ AdditionalMessage cMsg
    }

recursivePrograms :: [(String, String, String)]
recursivePrograms =
  [ ("p(X) :- p(X).", "self-recursive predicate is:", "p/1")
  , ("p(X) :- q(X). q(X) :- p(X).", "mutually recursive predicates are:", "p/1, q/1")
  , ("p(X) :- q(X). p(a). q(X) :- p(X).", "mutually recursive predicates are:", "p/1, q/1")
  , ("p(X) :- (q(X), r(X)); p(X).", "self-recursive predicate is:", "p/1")
  ]

errorFree :: [String]
errorFree =
  [ "p(X) :- q(X)."
  , "p(X) :- q(X). q(X) :- r(X)."
  , "p(X) :- q(X). q(X,Y) :- p(X)."
  ]

spec :: Spec
spec = describe "Recursion" $ do
  describe "Should detect recursive predicates" $
    forM_ recursivePrograms $ \(programCode, description, predicates') ->
      it programCode $
        shouldDetectProblemsStrict
          (caConfig Nothing)
          [ \problem ->
              isInfixOf "potentially makes use of recursion" problem
                && isInfixOf (description ++ "\n  " ++ predicates') problem
          ]
          programCode
  describe "Should not detect any problems" $
    forM_ errorFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems (caConfig Nothing) programCode
  it "should provide additional message when configured" $
    shouldDetectProblemsStrict
      (caConfig $ Just "Recursion is not part of this exercise yet.")
      [isInfixOf "Recursion is not part of this exercise yet."]
      "p(X) :- p(X)."
