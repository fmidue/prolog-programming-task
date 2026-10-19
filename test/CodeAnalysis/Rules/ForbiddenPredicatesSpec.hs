module CodeAnalysis.Rules.ForbiddenPredicatesSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Data.Set (Set)
import qualified Data.Set as Set (fromList)
import Language.Prolog (Signature (Signature))
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  ForbiddenPredicatesConfig (ForbiddenPredicatesConfig),
 )
import Prolog.Programming.Data (Code)
import Test.Hspec (Spec, describe, it)

caConfig :: Set Signature -> CodeAnalysisConfig
caConfig forbidden =
  emptyCodeAnalysisConfig {
    forbiddenPredicates = ForbiddenPredicatesConfig forbidden
    }

withProblems :: [(Code, Set Signature)]
withProblems =
  [ ("p(X) :- q(X).", Set.fromList [Signature "q" 1])
  , ("p(X) :- q(X), r(X).", Set.fromList [Signature "q" 1, Signature "r" 1])
  , ("p(X) :- q(X); r(X).", Set.fromList [Signature "q" 1, Signature "r" 1])
  , ("p(X) :- not(q(X)).", Set.fromList [Signature "not" 1])
  ]

detectionFree :: [(Code, Set Signature)]
detectionFree =
  [ ("p(X) :- q(X).", Set.fromList [Signature "p" 1])
  , ("p.", Set.fromList [Signature "p" 1])
  , ("p(X) :- q(X).", Set.fromList [Signature "r" 1])
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
    forM_ detectionFree $ \(programCode, forbidden) ->
      it programCode $
        shouldNotHaveProblems
          (caConfig forbidden)
          programCode
