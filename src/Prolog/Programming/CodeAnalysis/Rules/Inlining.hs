module Prolog.Programming.CodeAnalysis.Rules.Inlining (inliningChecker) where

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
  Substitution,
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
    ( \i@(term, _, _, goals') ->
        toProblem c term . fixedClause goals' <$> checkApplicable totalVars headVars i
    )
    information
  where
    totalVars = countVariables c
    headVars = countVariables clauseHead

    information = collectInformation goals Map.empty [] []
    fixedClause rhs sub =
      Clause (apply [sub] clauseHead) $ map (apply [sub]) $ reverse rhs
inliningChecker _ = []

{- | Collect information about candidate unifications.

For each unification whose two sides have disjoint variables, the result
records the unification, the variable-occurrence counts in the goals before
it, the counts in the goals after it, and the goals before it (in reversed order).
-}
collectInformation
  :: [Term]
  -- ^ Goals that have not been visited yet.
  -> Map String Int
  -- ^ Number of occurrences of each variable in the goals visited so far.
  -> [Term]
  -- ^ Goals visited so far (in reversed).
  -> [(Term, Map String Int, Map String Int, [Term])]
  {- ^ Candidate unifications collected so far.  Each tuple contains the
  unification, the variable counts in its prefix and suffix, and the goals
  in its prefix (in reversed order).
  -}
  -> [(Term, Map String Int, Map String Int, [Term])]
  {- ^ Candidate unifications together with their prefix and suffix
  information.
  -}
collectInformation [] _ _ us = us
collectInformation (t : ts) vs goals us =
  collectInformation ts (addVarsFromT vs) (t : goals) newUs'
  where
    addVarsFromT = Map.unionWith (+) (countVariables t)
    newUs =
      case t of
        Struct "=" [l, r]
          | Map.disjoint (countVariables l) (countVariables r) ->
              [(t, vs, Map.empty, goals)]
        _ -> []
    newUs' = newUs ++ map (\(t', p, s, goals') -> (t', p, addVarsFromT s, t : goals')) us

{- | Choose the variable side of a unification and the term to substitute for
it.

If both sides are variables, the variable with fewer total occurrences is
selected.  This keeps the substitution as small as possible while
preserving the unification.
-}
unification
  :: Map String Int
  -- ^ Number of occurrences of each variable in the whole clause.
  -> Term
  -- ^ Unification from which to select a variable and replacement term.
  -> (String, Term)
  -- ^ The selected variable name and the term that replaces it.
unification totalVars (Struct "=" [left, right]) = pick (var left) (var right)
  where
    var (Var (VariableName _ name)) = Just name
    var _ = Nothing

    pick :: Maybe String -> Maybe String -> (String, Term)
    pick (Just l) (Just r) = if Map.lookup l totalVars < Map.lookup r totalVars then (l, right) else (r, left)
    pick (Just l) Nothing = (l, right)
    pick Nothing (Just r) = (r, left)
    pick Nothing Nothing = error "Unification has no variable side"
unification _ _ = error "Only works on unification"

{- | Check whether a candidate unification satisfies one of the inlining
conditions and, if so, build its substitution.
-}
checkApplicable
  :: Map String Int
  -- ^ Number of occurrences of each variable in the whole clause.
  -> Map String Int
  -- ^ Number of occurrences of each variable in the clause head.
  -> (Term, Map String Int, Map String Int, [Term])
  {- ^ Candidate unification and the variable-occurrence counts in its
  prefix and suffix.
  -}
  -> Maybe Substitution
  {- ^ A substitution when the unification can be inlined; otherwise
  'Nothing'.
  -}
checkApplicable totalVars headVars (t, prefixVars, suffixVars, _)
  | Map.lookup uv headVars == Just 1 =
      -- rule 1
      if Map.disjoint tVars prefixVars && Map.notMember uv suffixVars
        then Just (VariableName 0 uv, ut)
        else Nothing
  | Map.notMember uv headVars =
      -- rule 2
      if Map.notMember uv prefixVars && 1 >= Map.findWithDefault 0 uv suffixVars && Map.disjoint tVars headVars
        then Just (VariableName 0 uv, ut)
        else Nothing
  | otherwise = Nothing
  where
    (uv, ut) = unification totalVars t
    tVars = countVariables t

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
