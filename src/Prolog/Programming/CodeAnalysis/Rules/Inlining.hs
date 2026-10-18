module Prolog.Programming.CodeAnalysis.Rules.Inlining (inliningChecker) where

import Control.Monad (guard)
import Data.Map (Map)
import qualified Data.Map as Map (
  disjoint,
  empty,
  findWithDefault,
  keysSet,
  lookup,
  notMember,
  unionWith,
 )
import qualified Data.Set as Set (empty, member, union)
import Data.Text.Lazy (pack)
import Language.Prolog (
  Clause (..),
  Term (..),
  VariableName (VariableName),
  substitute,
 )
import Prolog.Programming.CodeAnalysis.Helper (countVariables)
import Prolog.Programming.CodeAnalysis.Types (ClauseRule, Problem (..))
import Text.PrettyPrint.Leijen.Text (indent, string, vsep)

inliningChecker :: ClauseRule
inliningChecker (name, args, goals) =
  map
    ( \((_, l, r), replacement, goals') ->
        toProblem clause (Struct "=" [l, r]) $ fixedClause replacement goals'
    )
    $ collectUnifications totalVars headVars goals
  where
    clause = Clause name args goals
    clauseHead = Struct name args
    totalVars = Map.unionWith (+) headVars $ countVariables goals
    headVars = countVariables args

    fixedClause (x, term) rhs =
      let
        sub = (VariableName 0 x, term)
        substitutedHead = substitute sub clauseHead
      in
        case substitutedHead of
          Struct newName newArgs -> Clause newName newArgs $ map (substitute sub) rhs
          _ -> error "should not happen"

data Rule = One | Two deriving Eq

{- | Collect unifications that can be inlined (in reverse order).

For each unification whose two sides have disjoint variables and which satisfies
one of the inlining rules, the result records the rule matched, left and right
side of the unification, the selected variable and replacement, and the goals
besides it.
-}
collectUnifications
  :: Map String Int
  -- ^ Number of occurrences of each variable in the whole clause.
  -> Map String Int
  -- ^ Number of occurrences of each variable in the clause head.
  -> [Term]
  -- ^ Goals that have not been visited yet.
  -> [((Rule, Term, Term), (String, Term), [Term])]
  -- ^ Unifications (in reversed order) together with the goals besides them.
collectUnifications totalVars headVars goals =
  validate (collectCandidates goals Map.empty Map.empty Set.empty id []) Map.empty []
  where
    collectCandidates [] _ _ _ _ candidates = candidates
    collectCandidates (t : ts) vs nonUnificationVars unificationVars prefix candidates =
      collectCandidates
        ts
        (addVariables tVars vs)
        (if isUnification t then nonUnificationVars else addVariables tVars nonUnificationVars)
        (if isUnification t then Set.union (Map.keysSet tVars) unificationVars else unificationVars)
        (prefix . (t :))
        ((t, tVars, candidate) : candidates)
      where
        tVars = countVariables t
        candidate =
          case t of
            Struct "=" [l, r] -> do
              (rule, nameReplacement) <- satisfiesRuleAtOccurrence l r nonUnificationVars unificationVars
              pure ((rule, l, r), nameReplacement, prefix)
            _ -> Nothing

        isUnification (Struct "=" [_l, _r]) = True
        isUnification _ = False

        satisfiesRuleAtOccurrence l r previousNonUnificationVars previousUnificationVars = do
          let
            lVars = countVariables l
            rVars = countVariables r
          nameReplacement@(x, _term) <- unification totalVars l r
          guard $ Map.disjoint lVars rVars

          case Map.disjoint tVars headVars of
            True -> do
              guard $ Map.notMember x vs
              Just (Two, nameReplacement)
            False ->
              if Map.lookup x headVars == Just 1
                then do
                  guard $ Map.disjoint tVars previousNonUnificationVars
                  guard $ not (Set.member x previousUnificationVars)
                  Just (One, nameReplacement)
                else Nothing

    addVariables = Map.unionWith (+)

    validate [] _ _ = []
    validate ((t, tVars, candidate) : rest) suffix prependGoals =
      let
        valid = do
          ((rule, l, r), nameReplacement@(x, _), prefix) <- candidate
          let xCountInSuffix = Map.findWithDefault 0 x suffix

          guard $ (if rule == One then 0 else 1) == xCountInSuffix

          pure ((rule, l, r), nameReplacement, prefix prependGoals)
        suffix' = Map.unionWith (+) tVars suffix
        prependGoals' = t : prependGoals
      in
        case valid of
          Just result -> result : validate rest suffix' prependGoals'
          Nothing -> validate rest suffix' prependGoals'

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
toProblem originalClause equality fixedClause =
  Problem {
    problemDisplay =
      vsep
        [ string $ pack "Your clause"
        , indent 2 $ string $ pack $ show originalClause
        , string $ pack "uses the unification"
        , indent 2 $ string $ pack $ show equality
        , string $ pack "as a goal that can also directly be applied to the clause."
        , string $ pack "Doing that would result in:"
        , indent 2 $ string $ pack $ show fixedClause
        ]
    }
