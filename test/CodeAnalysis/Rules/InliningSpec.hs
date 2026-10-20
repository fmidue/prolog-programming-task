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

hasSuggestionsOnlyOneUnification :: [(String, [String])]
hasSuggestionsOnlyOneUnification =
  [ -- rule 1: unification without prefix
    ("p(Xs, X) :- Xs = [X,_].", ["p([X,_], X)."])
  , ("p([X]) :- X = a.", ["p([a])."])
  , ("p(X) :- X = leaf.", ["p(leaf)."])
  , ("p(X) :- leaf = X.", ["p(leaf)."])
  , ("p(X) :- X = node(L, V, R), q(V), p(L), p(R).", ["p(node(L, V, R)) :- q(V), p(L), p(R)."])
  , ("p(X) :- X = a, !.", ["p(a) :- !."])
  , ("p(X) :- X = a, (g(Y) ; q(Y)).", ["p(a) :- g(Y);q(Y)."])
  , ("p(X, Y) :- X = Y.", ["p(Y, Y)."])
  , ("p(X, Y) :- Y = X.", ["p(X, X)."])
  , ("p([X,Y|Ys], Zs) :- X = Y, p([Y|Ys], Zs).", ["p([Y,Y|Ys], Zs) :- p([Y|Ys], Zs)."])
  , ("p(X) :- X = b, q(a).", ["p(b) :- q(a)."])
  , ("p(X) :- X = [Y|Ys], q(Y), qs(Ys).", ["p([Y|Ys]) :- q(Y), qs(Ys)."])
  , ("p(X, X, Y) :- X = Y.", ["p(X, X, X)."])
  , ("p(X) :- X = aVeryLongAtomName.", ["p(aVeryLongAtomName)."])
  , -- rule 1: unification with prefixes containing only literals
    ("p(X) :- q(a), X = b.", ["p(b) :- q(a)."])
  , ("p(X) :- q(3), X = b.", ["p(b) :- q(3)."])
  , ("p(X) :- (g(Y), q(Y)), X = a, h(Y).", ["p(a) :- ,(g(Y), q(Y)), h(Y)."])
  , -- rule 2: unification without prefix
    ("p(Y) :- X = f(Y), q(X).", ["p(Y) :- q(f(Y))."])
  , ("p :- X = z, g(X), (a;b).", ["p :- g(z), a;b."])
  , ("p :- X = z, g(X), !.", ["p :- g(z), !."])
  , -- rule 2: unification with prefix
    ("p :- r, X = a, q(X, b).", ["p :- r, q(a, b)."])
  , ("p :- r, a = X, q(X, b).", ["p :- r, q(a, b)."])
  , ("p :- (a;b), X = z, g(X).", ["p :- a;b, g(z)."])
  , ("p :- !, X = z, g(X).", ["p :- !, g(z)."])
  ]

hasSuggestionsMultipleUnifications :: [(String, [String])]
hasSuggestionsMultipleUnifications =
  [ -- first unification does not match rule 1 because Y is used in suffix
    -- first unification does not match rule 2 because Y is used in clause head
    -- second unification matches rule 1
    ("p(X, Y) :- Y = [Z], q(Y), X = a.", ["p(a, Y) :- Y = [Z], q(Y)."])
  , -- first unification matches rule 1
    -- second unification matches rule 1
    ("p(X, Y) :- X = a, Y = b.", ["p(a, Y) :- Y = b.", "p(X, b) :- X = a."])
  , -- the first unification does not match rule 1 as Y is used in it's suffix
    -- the first unification does not match rule 2 as Y is used in clause head
    -- the second unification matches rule 1
    -- the third unification does not match rule 1 as Z is not in clause head
    -- the third unification does not match rule 2 as Z is used in it's prefix
    ("p(X, Y) :- Y = f(Z), X = f(Y), Z = 3.", ["p(f(Y), Y) :- Y = f(Z), Z = 3."])
  , --  the first unification does not match rule 1 as A is not in clause head
    --  the first unification does not match rule 2 as A is not used in it's suffix
    --  the second unification does match rule 2
    ("p :- A = b, r, X = c, q(X).", ["p :- A = b, r, q(c)."])
  , --  the first unification does not match rule 1 as A is not in clause head
    --  the first unification does not match rule 2 as A is not used in it's suffix
    --  the second unification does match rule 2
    ("p :- A = b, (r, X = c, q(X)).", ["p :- A = b, r, q(c)."])
  , -- the first unification matches rule 2
    -- the second unification does not match rule 1 because it is not used in the clause head
    -- the second unification does not match rule 2 because X is used in it's prefix
    ("p :- X = Y, X = a.", ["p :- Y = a."])
  , -- the first unification matches rule 2
    -- the second unification matches rule 2
    ("p :- X = a, Y = b, g(Y), q(X).", ["p :- Y = b, g(Y), q(a).", "p :- X = a, g(b), q(X)."])
  , -- first and second unification is not tracked because they are part of an explicit conjunction
    -- the third unification matches rule 1
    ("p(X) :- (A = B, C = D), X = a.", ["p(a) :- ,(A = B, C = D)."])
  , -- the first unification matches rule 2
    -- the second unification does not match rule 1 because V and W are not used in the clause head
    -- the second unification does not match rule 2 because V and W are not used in the suffix
    -- the third unification matches rule 1
    ("p(X) :- U = Z, V = W, X = f(Z).", ["p(X) :- V = W, X = f(U).", "p(f(Z)) :- U = Z, V = W."])
  , -- the first unification matches rule 1
    -- the second unification matches rule 2
    ("p(X, Y) :- X = a, q(Y), Z = Y, r(Z).", ["p(a, Y) :- q(Y), Z = Y, r(Z).", "p(X, Y) :- X = a, q(Y), r(Y)."])
  ]

hasViolationsOnlyOneUnification :: [String]
hasViolationsOnlyOneUnification =
  [ -- both rules: unification variable contained in replacement term
    "p(X) :- X = [X]."
  , "p(X) :- X = f(X)."
  , "p :- X = [X]."
  , "p :- X = f(X)."
  , -- rule 1: X used in suffix
    -- rule 2: X used in clause head
    "p(X, Y) :- X = a, q(X, Y)."
  , -- rule 1: unification variable used in prefix
    "p(Xs, X) :- Xs = [X,_], q(Xs)."
  , "p(X) :- q(X), X = a, r(X)."
  , "p(X, Y) :- X = f(A, B), q(X, Y)."
  , -- rule 1: unification variable does not occur exactly once in head
    "p(X, X) :- X = f(g(c))."
  , "p(Y) :- X = f(Y)."
  , -- rule 1: unification or term variables used in literal prefix
    "p(X) :- q(X), X = [a]."
  , "p(X, Y) :- q(X, Y), X = f(Y)."
  , "p(X) :- q(X), X = a."
  , "p(X, Y) :- b(X, Y), X = Y, q(X, Y)."
  , "p(X, Y) :- q(Y), X = [Y]."
  , "p(X, Y) :- not(q(Y)), X = [Y]."
  , -- rule 1: prefix contains disallowed operators
    "p(X) :- q(X), !, X = a."
  , "p(X) :- (q(X) ; r(X)), X = a."
  , "p(X) :- !, X = a."
  , "p(X, Y) :- (q(Y) ; r(Y)), X = a."
  , -- rule 2: unification variable does not occur exactly once in suffix
    "p :- r, X = a, q(X), d(X)."
  , "p :- r, X = a, (q(X), d(X))."
  , "p :- X = a."
  ]

hasViolationsMultipleUnifications :: [String]
hasViolationsMultipleUnifications =
  [ -- the first unification does not match rule 1 as Z is not in clause head
    -- the first unification does not match rule 2 as Z is not used in it's suffix
    -- the second unification does not match rule 1 as X is used in it's prefix
    -- the second unification does not match rule 2 as X is used in clause head
    "p(X, Y) :- Z = f(X), X = f(Y)."
  , -- the first unification does not match rule 1 as Z is not in clause head
    -- the first unification does not match rule 2 as Z is not used in it's suffix
    -- the second unification does not match rule 1 as X is in clause head
    -- the second unification does not match rule 2 as X is used in it's suffix
    "p :- Z = f(X), X = a, q(X)."
  , -- the first unification does not match rule 1 as Y or U is not in clause head
    -- the first unification does not match rule 2 as Y and U are used twice in their suffix
    -- the second unification does not match rule 1 as U is used in the prefix
    -- the second unification does not match rule 2 as X is in the clause head
    "p(X) :- Y = U, not(q(Y)), X = f(U), p(Y, U)."
  , -- the first unification does not match rule 1 as Y or U is not in clause head
    -- the first unification does not match rule 2 as Y and U are used twice in their suffix
    -- the second unification does not match rule 1 as U is used in the prefix
    -- the second unification does not match rule 2 as X is in the clause head
    "p(X) :- Y = U, q(Y), X = f(U), p(Y, U)."
  , -- the first unification is not tracked as a candidate as it is part of a conjunction
    -- the second unification does not match rule 1 as U is used in the prefix
    -- the second unification does not match rule 2 as X is in the clause head
    "p(X) :- (Y = U, q(Y)), X = f(U), p(Y, U)."
  , -- the first unification does not match rule 1 as Y is used twice in the clause head
    -- the first unification does not match rule 2 as Y is used in the clause head
    -- the second unification does not match rule 1 as Z is not used in the clause head
    -- the second unification does not match rule 2 as Z is used in it's prefix
    -- it should also not match the not yet covered third rule
    "p(f(Y), Y) :- Y = f(Z), q(Y), Z = 3."
  ]

notCovered :: [String]
notCovered =
  [ -- Z = 3 could be inlined
    "p(f(Y), Y) :- Y = f(Z), Z = 3."
  ]

noUnificationsWithVariables :: [String]
noUnificationsWithVariables =
  [ "p(X) :- q(X)."
  , "p(X) :- X =:= a."
  , "p(X) :- a = b, q(X)."
  ]

detects :: [(String, [String])] -> Spec
detects cases =
  forM_ cases $ \(programCode, expectedFixedClauses) ->
    it programCode $
      shouldDetectProblemsStrict
        caConfig
        ( map
            ( \fixedClause display ->
                isInfixOf "as a goal that can also directly be applied to the clause." display
                  && isInfixOf fixedClause display
            )
            expectedFixedClauses
        )
        programCode

doesNotDetect :: [String] -> Spec
doesNotDetect cases =
  forM_ cases $ \programCode ->
    it programCode $
      shouldNotHaveProblems caConfig programCode

spec :: Spec
spec = describe "Inlining" $ do
  describe "One unification exists and can be inlined" $
    detects hasSuggestionsOnlyOneUnification
  describe "Multiple unifications exists and at least one can be inlined" $
    detects hasSuggestionsMultipleUnifications
  describe "One unification exist and cannot be inlined" $
    doesNotDetect hasViolationsOnlyOneUnification
  describe "Multiple unifications exist and cannot be inlined" $
    doesNotDetect hasViolationsMultipleUnifications
  describe "Does not suggest inlining for uncovered opportunities" $
    doesNotDetect notCovered
  describe "Does not suggest inlining when there are no unifications (with variables)" $
    doesNotDetect noUnificationsWithVariables
