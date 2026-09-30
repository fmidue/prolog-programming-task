{-# LANGUAGE QuasiQuotes #-}

module CodeAnalysis.Rules.UngroupedDefinitionsSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  Severity (..),
  UngroupedDefinitionsConfig (UngroupedDefinitionsConfig),
 )
import Test.Hspec (Spec, describe, it, shouldBe)

import Language.Prolog (consultString)
import qualified Text.RawString.QQ as RS (r)

caConfig :: CodeAnalysisConfig
caConfig =
  emptyCodeAnalysisConfig {
    ungroupedDefinitions = UngroupedDefinitionsConfig $ Detect Hint ()
    }

spec :: Spec
spec = do
  describe "Prolog Parser" $ do
    it "parses the clauses in order of definition" $
      map show
        <$> consultString
          [RS.r|
a.
a(X) :- b(X).
b(X, Y) :- X > Y.
      |]
        `shouldBe` Right ["a.", "a(X) :- b(X).", "b(X, Y) :- X > Y."]
  describe "UngroupedDefinitions" $ do
    it "Should detect ungrouped definitions" $
      shouldDetectProblemsStrict
        caConfig
        [(== "Your code does not group predicate definitions by predicate name.")]
        [RS.r|
nonNegative(0).
nonPositive(0).

nonNegative(X) :- X > 0.
nonPositive(X) :- X < 0.
        |]
    it "Should detect ungrouped definitions with different arities" $
      shouldDetectProblemsStrict
        caConfig
        [(== "Your code does not group predicate definitions by predicate name.")]
        [RS.r|
a(0).
b(0).
a(1,2).
        |]
    it "Should not detect any problems when definitions are grouped" $
      shouldNotHaveProblems
        caConfig
        [RS.r|
nonPositive(0).
nonPositive(X) :- X < 0.

nonNegative(0).
nonNegative(X) :- X > 0.
        |]
    it "Should detect grouped definitions without ascending arity of definitions" $
      shouldDetectProblemsStrict
        caConfig
        [(== "Your code does not sort the predicate definitions ascending by arity (per group).")]
        [RS.r|
a(0).
a(1,2).
a(3).
b(4).
        |]
    it "Should not detect any problems when definitions are sorted ascending in arity" $
      shouldNotHaveProblems
        caConfig
        [RS.r|
a(0).
a(3).
a(1,2).
b(4).
        |]
