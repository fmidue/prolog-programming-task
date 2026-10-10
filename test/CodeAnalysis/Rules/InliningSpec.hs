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
  [ ("p(Xs,X) :- Xs = [X,_].", "p([X,_], X).") -- Fulfills rule 1
  , ("p([X]) :- X = a.", "p([a]).") -- Fulfills rule 1
  , ("p(X) :- X = leaf.", "p(leaf).") -- Fulfills rule 1
  , ("p(X) :- leaf = X.", "p(leaf).") -- Fulfills rule 1
  ,
    ( "p(X) :- X = node(L,V,R), q(V), p(L), p(R)." -- Fulfills rule 1
    , "p(node(L, V, R)) :- q(V), p(L), p(R)."
    )
  , ("p(X) :- X = a, !.", "p(a) :- !.") -- Fulfills rule 1
  , ("p(X,Y) :- X = Y.", "p(X, X).") -- Fulfills rule 1
  , ("p(X) :- q(a), X = b. p(b).", "p(b) :- q(a).") -- Fulfills rule 1
  , ("p(X) :- !, X = a.", "p(a) :- !.") -- Fulfills rule 1
  , ("p([X,Y|Ys], Zs) :- X = Y, p([Y|Ys], Zs).", "p([Y,Y|Ys], Zs) :- p([Y|Ys], Zs).") -- Fulfills rule 1
  , ("p(X) :- X = b, q(a).", "p(b) :- q(a).") -- Fulfills rule 1
  , ("p(X) :- X = [Y|Ys], q(Y), qs(Ys).", "p([Y|Ys]) :- q(Y), qs(Ys).") -- Fulfills rule 1
  , ("p(X,X,Y) :- X = Y.", "p(X, X, X).") -- Fulfills rule 1
  , ("p :- r, X = a, q(X, b).", "p :- r, q(a, b).") -- Fulfills rule 2
  , ("p :- r, a = X, q(X, b).", "p :- r, q(a, b).") -- Fulfills rule 2
  , ("p(X) :- X = aVeryLongAtomName.", "p(aVeryLongAtomName).") -- Fulfills rule 1
  , ("p(X,Y) :- Y = [Z], q(Y), X = a.", "p(a, Y) :- Y = [Z], q(Y).") -- Fulfills rule 1
  ]

detectionFree :: [String]
detectionFree =
  [ "p(Xs,X) :- Xs = [X,_], q(Xs)." -- Xs used after unification
  , "p(X) :- q(X), X = [a]." -- first predicate contains variable in unification
  , "p(X,Y) :- q(Y), X = [Y]." -- first predicate contains variable in unification
  , "p(X,Y) :- not(q(Y)), X = [Y]." -- first predicate contains variable in unification
  , "p(X,Y) :- q(X,Y), X = f(Y)." -- first predicate contains variable in unification
  , "p(X) :- (q(X) ; r(X)), X = a." -- first predicate contains variable in unification
  , "p(X) :- q(X), X = a, r(X)." -- first predicate contains variable in unification
  , "p(X) :- q(X), !, X = a. p(b)." -- first predicate contains variable in unification
  , "p(X) :- q(X), X = a. p(a) :- !." -- first predicate contains variable in unification
  , "p(X) :- X = [X]." -- term includes X
  , "p(X) :- X =:= a." -- =:= operator not tracked
  , "p(X) :- q(X)." -- no unification
  , "p(X,Y) :- b(X,Y), X = Y, q(X,Y)." -- X used in head and in first predicate
  , "p(X, Y) :- X = f(A,B), q(X,Y)." -- X used after unification
  , "p(X, Y) :- X = f(X), q(X,Y)." -- term includes X
  , "p(X, Y) :- X = a, q(X,Y)." -- X used after unification
  , "p :- r, X = a, q(X), d(X)." -- X used twice after unification
  , "p(X,X) :- X = f(g(c))." -- X used twice in head
  ]

spec :: Spec
spec = describe "Inlining" $ do
  describe "Should detect terms that can be inlined into the clause head" $
    forM_ detectsPatternMatches $ \(programCode, expectedFixedClause) ->
      it programCode $
        shouldDetectProblemsStrict
          caConfig
          [ \display ->
              isInfixOf "as a goal that can also directly be applied to the clause." display
                && isInfixOf expectedFixedClause display
          ]
          programCode
  describe "Should not detect unsafe or unrelated equalities" $
    forM_ detectionFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems
          caConfig
          programCode
