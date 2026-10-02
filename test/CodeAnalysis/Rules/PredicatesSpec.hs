module CodeAnalysis.Rules.PredicatesSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Data.Set (fromList)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  ForbiddenPredicate (ForbiddenPredicate),
  ForbiddenPredicates (ForbiddenPredicates),
  PredicatesConfig (PredicatesConfig),
  Severity (..),
 )
import Test.Hspec (Spec, describe, it)

caConfig :: [(String, Int)] -> CodeAnalysisConfig
caConfig forbidden =
  emptyCodeAnalysisConfig {
    predicates = PredicatesConfig $ Detect Hint $ ForbiddenPredicates (fromList (map ForbiddenPredicate forbidden))
    }

withProblems :: [(String, [(String, Int)])]
withProblems =
  [ ("p(X) :- q(X).", [("q", 1)])
  , ("p(X) :- q(X), r(X).", [("q", 1), ("r", 1)])
  , ("p(X) :- q(X); r(X).", [("q", 1), ("r", 1)])
  ]

errorFree :: [(String, [(String, Int)])]
errorFree =
  [ ("p(X) :- q(X).", [("p", 1)])
  , ("p.", [("p", 1)])
  , ("p(X) :- q(X).", [("r", 1)])
  ]

spec :: Spec
spec = describe "Predicates" $ do
  describe "Should detect forbidden predicate usage" $
    forM_ withProblems $ \(programCode, forbidden) ->
      it programCode $
        shouldDetectProblemsStrict
          (caConfig forbidden)
          [ \problem ->
              isInfixOf "makes use of forbidden predicates" problem
                && all (\(name, arity) -> (name ++ "/" ++ show arity) `isInfixOf` problem) forbidden
          ]
          programCode
  describe "Should not detect forbidden predicates in safe clauses" $
    forM_ errorFree $ \(programCode, forbidden) ->
      it programCode $
        shouldNotHaveProblems
          (caConfig forbidden)
          programCode
