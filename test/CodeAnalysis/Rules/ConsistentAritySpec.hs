module CodeAnalysis.Rules.ConsistentAritySpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldDetectProblemsStrict', shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  ConsistentArityConfig (ConsistentArityConfig),
  CutUsageConfig (..),
  IgnoredPredicates (IgnoredPredicates),
  Severity (..),
  SingletonVariablesConfig (..),
 )
import Test.Hspec (Spec, describe, it)

caConfig :: [String] -> CodeAnalysisConfig
caConfig predicates =
  CodeAnalysisConfig {
    singletonVariables =
      SingletonVariablesConfig Ignore
    , cutUsage =
        CutUsageConfig Ignore
    , consistentArity = ConsistentArityConfig $ Detect Hint $ IgnoredPredicates predicates
    }

hasMultiple :: [(String, [String])]
hasMultiple =
  [ ("p(X) :- q(Y), p(X,Y).", ["p"])
  , ("p(X) :- q(X). p(X,Y) :- w(X,Y).", ["p"])
  , ("p(X) :- q(Y), w(Y,[V|Vs]), p(V,Vs), q(X,V).", ["p", "q"])
  , ("p(X) :- q(Y), (p(X,Y), w(X,Y)).", ["p"])
  , ("p(X) :- q(Y), (p(X,Y); w(X,Y)).", ["p"])
  ]

errorFree :: [String]
errorFree =
  [ "p."
  , "p(_)."
  , "p(X) :- q(X)."
  , "p(_) :- q(Y), p(Y)."
  , "p(X,Y) :- q(X), p(Y,X)."
  , "p(node(L,R)) :- q(L), q(R). u(node(L,_)) :- w(L)."
  , "p(node(L,R)) :- q(L), q(R). u(node(_,V,_)) :- w(V)."
  , "p(X) :- X = node(L,R), q(L), q(R). u(node(_,V,_)) :- w(V)."
  ]

spec :: Spec
spec = describe "ConsistentArity" $ do
  describe "Should detect multiple arities" $
    forM_ hasMultiple $ \(programCode, predicates) ->
      it programCode $
        shouldDetectProblemsStrict
          (caConfig [])
          (map (isInfixOf . ("Your program contains the predicate " ++)) predicates)
          programCode
  describe "Should not detect any problems" $
    forM_ errorFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems
          (caConfig [])
          programCode
  it "should ignore predicate when configured" $
    shouldNotHaveProblems
      (caConfig ["p"])
      "p(X) :- q(Y), p(X,Y)."
  it "should detect violation of forced arity" $
    shouldDetectProblemsStrict'
      (caConfig [])
      [isInfixOf "check which is used/defined with wrong arity. It should be check/2."]
      "p(X) :- check(X)."
      "check(_,_)."
