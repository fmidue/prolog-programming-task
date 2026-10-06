module CodeAnalysis.Rules.RhsPatternMatchingSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  RhsPatternMatchingConfig (..),
  Severity (..),
  WithSeverity (..),
 )
import Test.Hspec (Spec, describe, it)

caConfig :: CodeAnalysisConfig
caConfig =
  emptyCodeAnalysisConfig {
    rhsPatternMatching =
      RhsPatternMatchingConfig $ Just $ WithSeverity Hint ()
    }

detectsPatternMatches :: [(String, String)]
detectsPatternMatches =
  [ ("p(Xs,X) :- Xs = [X,_].", "p([X,_], X).")
  , ("p([X]) :- X = a.", "p([a]).")
  , ("p(X) :- X = leaf.", "p(leaf).")
  , ("p(X) :- leaf = X.", "p(leaf).")
  ,
    ( "p(X) :- X = node(L,V,R), q(V), p(L), p(R)."
    , "p(node(L, V, R)) :- q(V), p(L), p(R)."
    )
  , ("p(X) :- X = a, !.", "p(a) :- !.")
  ]

errorFree :: [String]
errorFree =
  [ "p(Xs,X) :- Xs = [X,_], q(Xs)."
  , "p(X) :- q(X), X = [a]."
  , "p(X,Y) :- q(Y), X = [Y]."
  , "p(X,Y) :- not(q(Y)), X = [Y]."
  , "p(X,Y) :- q(X,Y), X = f(Y)."
  , "p(X) :- (q(X) ; r(X)), X = a."
  , "p(X) :- q(X), X = a, r(X)."
  , "p(X) :- !, X = a."
  , "p(X) :- q(a), X = b. p(b)."
  , "p(X) :- q(X), !, X = a. p(b)."
  , "p(X) :- q(X), X = a. p(a) :- !."
  , "p(X) :- X = [X]."
  , "p(X) :- X =:= a."
  , "p(X) :- q(X)."
  ]

spec :: Spec
spec = describe "RhsPatternMatching" $ do
  describe "Should detect pattern matching on the RHS" $
    forM_ detectsPatternMatches $ \(programCode, expectedFixedClause) ->
      it programCode $
        shouldDetectProblemsStrict
          caConfig
          [ \display ->
              isInfixOf "can be moved to the left-hand side" display
                && isInfixOf expectedFixedClause display
          ]
          programCode
  describe "Should not detect unsafe or unrelated equalities" $
    forM_ errorFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems
          caConfig
          programCode
