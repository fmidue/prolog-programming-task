module CodeAnalysis.Rules.InliningSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  InliningConfig (..),
  Severity (..),
  WithSeverity (..),
 )
import Test.Hspec (Spec, describe, it)

caConfig :: CodeAnalysisConfig
caConfig =
  emptyCodeAnalysisConfig {
    inlining =
      InliningConfig $ Just $ WithSeverity Hint ()
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
  , ("p(X,Y) :- X = Y.", "p(Y, Y).")
  ]

detectionFree :: [String]
detectionFree =
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
spec = describe "Inlining" $ do
  describe "Should detect terms that can be inlined into the clause head" $
    forM_ detectsPatternMatches $ \(programCode, expectedFixedClause) ->
      it programCode $
        shouldDetectProblemsStrict
          caConfig
          [ \display ->
              isInfixOf "as its first goal which can be inlined into the clause head." display
                && isInfixOf expectedFixedClause display
          ]
          programCode
  describe "Should not detect unsafe or unrelated equalities" $
    forM_ detectionFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems
          caConfig
          programCode
