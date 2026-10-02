module CodeAnalysis.Rules.InconsistentAritiesSpec where

import CodeAnalysis.Helper (
  shouldDetectProblemsStrict,
  shouldDetectProblemsStrict',
  shouldNotHaveProblems,
  shouldNotHaveProblems',
 )
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  IgnoredPredicates (IgnoredPredicates),
  InconsistentAritiesConfig (InconsistentAritiesConfig),
  Severity (..),
 )
import Test.Hspec (Spec, describe, it)

caConfig :: [String] -> CodeAnalysisConfig
caConfig predicates' =
  emptyCodeAnalysisConfig {
    inconsistentArities = InconsistentAritiesConfig $ Detect Hint $ IgnoredPredicates predicates'
    }

hasMultiple :: [(String, [String])]
hasMultiple =
  [ ("p(X) :- q(Y), p(X,Y).", ["p"])
  , ("p(X) :- q(X). p(X,Y) :- w(X,Y).", ["p"])
  , ("p(X) :- q(Y), w(Y,[V|Vs]), p(V,Vs), q(X,V).", ["p", "q"])
  , ("p(X) :- q(Y), (p(X,Y), w(X,Y)).", ["p"])
  , ("p(X) :- q(Y), (p(X,Y); w(X,Y)).", ["p"])
  , ("p(X) :- not(p(X,_)).", ["p"])
  , ("p(X) :- \\+ p(X,_).", ["p"])
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

ignores :: [(String, [String])]
ignores =
  [ ("p(X) :- q(Y), p(X,Y).", ["p"])
  , ("'predicate with spaces' :- q(X), 'predicate with spaces'(X).", ["predicate with spaces"])
  ]

spec :: Spec
spec = describe "InconsistentArities" $ do
  describe "Should detect multiple arities" $
    forM_ hasMultiple $ \(programCode, predicates') ->
      it programCode $
        shouldDetectProblemsStrict
          (caConfig [])
          (map (isInfixOf . ("Your program contains the predicate " ++)) predicates')
          programCode
  describe "Should not detect any problems" $
    forM_ errorFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems
          (caConfig [])
          programCode
  describe "should ignore predicates when configured" $
    forM_ ignores $ \(programCode, predicates') ->
      it programCode $
        shouldNotHaveProblems
          (caConfig predicates')
          programCode
  it "should ignore predicates in task/hidden definitions when configured" $
    shouldNotHaveProblems'
      (caConfig ["p"])
      "w."
      "p(X) :- q(Y), p(X,Y)."
  it "should detect violation of forced arity" $
    shouldDetectProblemsStrict'
      (caConfig [])
      [isInfixOf "check which is used/defined with wrong arity. It should be check/2."]
      "p(X) :- check(X)."
      "check(_,_)."
