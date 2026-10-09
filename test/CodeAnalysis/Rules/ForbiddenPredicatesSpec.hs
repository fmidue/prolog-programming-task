module CodeAnalysis.Rules.ForbiddenPredicatesSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Data.Set (Set)
import qualified Data.Set as Set (fromList)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  ForbiddenPredicatesConfig (ForbiddenPredicatesConfig),
  Predicate (..),
 )
import Prolog.Programming.Data (Code)
import Test.Hspec (Spec, describe, it)

caConfig :: Set Predicate -> CodeAnalysisConfig
caConfig forbidden =
  emptyCodeAnalysisConfig {
    forbiddenPredicates = ForbiddenPredicatesConfig forbidden
    }

withProblems :: [(Code, Set Predicate)]
withProblems =
  [ ("p(X) :- q(X).", Set.fromList [Predicate "q" 1])
  , ("p(X) :- q(X), r(X).", Set.fromList [Predicate "q" 1, Predicate "r" 1])
  , ("p(X) :- q(X); r(X).", Set.fromList [Predicate "q" 1, Predicate "r" 1])
  , ("p(X) :- not(q(X)).", Set.fromList [Predicate "not" 1])
  ]

errorFree :: [(Code, Set Predicate)]
errorFree =
  [ ("p(X) :- q(X).", Set.fromList [Predicate "p" 1])
  , ("p.", Set.fromList [Predicate "p" 1])
  , ("p(X) :- q(X).", Set.fromList [Predicate "r" 1])
  ]

spec :: Spec
spec = describe "Forbidden predicates" $ do
  describe "Should detect forbidden predicate usage" $
    forM_ withProblems $ \(programCode, forbidden) ->
      it programCode $
        shouldDetectProblemsStrict
          (caConfig forbidden)
          [ \problem ->
              isInfixOf "makes use of forbidden predicates" problem
                && all (\predicate -> show predicate `isInfixOf` problem) forbidden
          ]
          programCode
  describe "Should not detect forbidden predicates in safe clauses" $
    forM_ errorFree $ \(programCode, forbidden) ->
      it programCode $
        shouldNotHaveProblems
          (caConfig forbidden)
          programCode
