module Prolog.Programming.CodeAnalysis.Rules.Inlining (inliningChecker) where

import Control.Monad (guard)
import Data.Map (Map)
import qualified Data.Map as Map (
  disjoint,
  empty,
  findWithDefault,
  lookup,
  notMember,
  unionWith,
 )
import Data.Maybe (mapMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (
  Clause (..),
  Term (..),
  VariableName (VariableName),
  apply,
 )
import Prolog.Programming.CodeAnalysis.Helper (countVariables)
import Prolog.Programming.CodeAnalysis.Types (ClauseRule, Problem (..))
import Text.PrettyPrint.Leijen.Text (indent, string, vsep)

inliningChecker :: ClauseRule
inliningChecker c@(Clause clauseHead goals) =
  mapMaybe
    ( \((_, l, r), _, goals') -> do
        replacement <- unification totalVars l r
        pure $ toProblem c (Struct "=" [l, r]) $ fixedClause goals' replacement
    )
    information
  where
    totalVars = countVariables c
    headVars = countVariables clauseHead

    information = collectUnifications headVars goals Map.empty [] []
    fixedClause rhs (name, replacement) =
      let sub = (VariableName 0 name, replacement)
      in Clause (apply [sub] clauseHead) $ map (apply [sub]) $ reverse rhs
inliningChecker _ = []

data Rule = One | Two deriving Eq

{- | Collect unifications that can be inlined.

For each unification whose two sides have disjoint variables and which satisfies
one of the inlining rules, the result records the rule matched, left and right
side of the unification, the variable-occurrence counts in the goals after it,
and the goals besides it (in reversed order).
-}
collectUnifications
  :: Map String Int
  -- ^ Number of occurrences of each variable in the clause head.
  -> [Term]
  -- ^ Goals that have not been visited yet.
  -> Map String Int
  -- ^ Number of occurrences of each variable in the goals visited so far.
  -> [Term]
  -- ^ Goals visited so far (in reversed).
  -> [((Rule, Term, Term), Map String Int, [Term])]
  {- ^ Candidate unifications collected so far.  Each tuple contains the candidate rule, the
  left and right side of the unification, the variable counts in its suffix, and the goals
  besides the unification (in reversed order).
  -}
  -> [((Rule, Term, Term), Map String Int, [Term])]
  {- ^ Unifications together with their prefix and suffix
  information.
  -}
collectUnifications _ [] vs _ us = mapMaybe discardOrUpdate us
  where
    discardOrUpdate i@((rule, l, r), suffixVars, _) = do
      (uv, _) <- unification vs l r
      let expected = if rule == One then 0 else 1

      let uvCountInSuffix = Map.findWithDefault 0 uv suffixVars

      guard $ expected == uvCountInSuffix

      Just i
collectUnifications headVars (t : ts) vs goals us =
  collectUnifications headVars ts (addVarsFromT vs) (t : goals) newUs'
  where
    addVarsFromT = Map.unionWith (+) (countVariables t)
    newUs =
      case t of
        Struct "=" [l, r] -> case satisfiesRuleAtOccurrence l r of
          Just rule -> [((rule, l, r), Map.empty, goals)]
          Nothing -> []
        _ -> []
    newUs' = newUs ++ map (\(t', s, goals') -> (t', addVarsFromT s, t : goals')) us

    satisfiesRuleAtOccurrence l r = do
      let tVars = countVariables t
      (uv, _ut) <- unification vs l r
      guard $ Map.disjoint (countVariables l) (countVariables r)

      case Map.disjoint tVars headVars of
        True -> do
          guard $ Map.notMember uv vs
          Just Two
        False ->
          if Map.lookup uv headVars == Just 1
            then do
              guard $ Map.disjoint tVars vs
              Just One
            else Nothing

{- | Choose the variable side of a unification and the term to substitute for
it.

If both sides are variables, the variable with fewer total occurrences is
selected; if their counts are equal, the right-hand variable is selected.
This keeps the substitution as small as possible while preserving the
unification. Returns 'Nothing' when neither side is a variable.
-}
unification
  :: Map String Int
  -- ^ Number of occurrences of each variable in the whole clause.
  -> Term
  -- ^ Left side of unification to select from
  -> Term
  -- ^ Right side of unification to select from
  -> Maybe (String, Term)
  -- ^ The selected variable name and the term that replaces it.
unification totalVars left right = pick (var left) (var right)
  where
    var (Var (VariableName _ name)) = Just name
    var _ = Nothing

    pick :: Maybe String -> Maybe String -> Maybe (String, Term)
    pick (Just l) (Just r) = Just $ if Map.lookup l totalVars < Map.lookup r totalVars then (l, right) else (r, left)
    pick (Just l) Nothing = Just (l, right)
    pick Nothing (Just r) = Just (r, left)
    pick Nothing Nothing = Nothing

toProblem :: Clause -> Term -> Clause -> Problem
toProblem originalClause term fixedClause =
  Problem {
    problemDisplay =
      vsep
        [ string $ pack "Your clause"
        , indent 2 $ string $ pack $ show originalClause
        , string $ pack "uses the unification"
        , indent 2 $ string $ pack $ show term
        , string $ pack "as a goal that can also directly be applied to the clause."
        , string $ pack "Doing that would result in:"
        , indent 2 $ string $ pack $ show fixedClause
        ]
    }
