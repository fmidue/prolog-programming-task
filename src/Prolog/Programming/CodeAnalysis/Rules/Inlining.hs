module Prolog.Programming.CodeAnalysis.Rules.Inlining (inliningChecker) where

import Control.Applicative (asum)
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
import Prolog.Programming.CodeAnalysis.Helper (containsCut, countVariables)
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

{- | Collect unifications that can be inlined.

For each unification whose two sides have disjoint variables and which satisfies
one of the inlining rules, the result records the rule matched, left and right
side of the unification, the selected variable and replacement term, and the goals
besides it.
-}
collectUnifications
  :: Map String Int
  -- ^ Number of occurrences of each variable in the whole clause.
  -> Map String Int
  -- ^ Number of occurrences of each variable in the clause head.
  -> [Term]
  -- ^ Goals in the clause's right-hand side.
  -> [((Rule, Term, Term), (String, Term), [Term])]
  -- ^ Unifications together with the goals besides them.
collectUnifications totalVars headVars goals =
  validate (collectCandidates goals Map.empty Map.empty Set.empty False id []) Map.empty [] []
  where
    collectCandidates [] _ _ _ _ _ candidates = candidates
    collectCandidates (t : ts) vs nonUnificationVars unificationVars prefixHasDisallowedOperator prefix candidates =
      collectCandidates
        ts
        (addVariables tVars vs)
        (if isStructWithName "=" t then nonUnificationVars else addVariables tVars nonUnificationVars)
        (if isStructWithName "=" t then Set.union (Map.keysSet tVars) unificationVars else unificationVars)
        (prefixHasDisallowedOperator || isStructWithName ";" t || containsCut t)
        (prefix . (t :))
        ((t, tVars, candidate) : candidates)
      where
        tVars = countVariables t
        candidate =
          case t of
            Struct "=" [l, r] -> do
              (rule, replacement) <-
                satisfiesRuleAtOccurrence
                  l
                  r
                  nonUnificationVars
                  unificationVars
                  prefixHasDisallowedOperator
              pure ((rule, l, r), replacement, prefix)
            _ -> Nothing

        isStructWithName name (Struct name' _) = name == name'
        isStructWithName _ _ = False

        satisfiesRuleAtOccurrence
          l
          r
          previousNonUnificationVars
          previousUnificationVars
          prefixHasDisallowedOp = do
            let
              lVars = countVariables l
              rVars = countVariables r
            guard $ Map.disjoint lVars rVars
            asum $ map chooseRule $ unificationCandidates totalVars l r
            where
              chooseRule replacement@(x, _term) =
                case Map.lookup x headVars of
                  Nothing -> do
                    guard $ Map.notMember x vs
                    guard $ suffixCount x == 1
                    Just (Two, replacement)
                  Just 1 -> do
                    guard $ not prefixHasDisallowedOp
                    guard $ suffixCount x == 0
                    guard $ Map.disjoint tVars previousNonUnificationVars
                    guard $ not (Set.member x previousUnificationVars)
                    Just (One, replacement)
                  _ ->
                    Nothing

              suffixCount x =
                Map.findWithDefault 0 x totalVars
                  - Map.findWithDefault 0 x headVars
                  - Map.findWithDefault 0 x vs
                  - Map.findWithDefault 0 x tVars

    addVariables = Map.unionWith (+)

    validate [] _ _ confirmed = confirmed
    validate ((t, tVars, candidate) : rest) suffixVars suffixGoals confirmed =
      let
        valid = do
          ((rule, l, r), replacement@(x, _), prefix) <- candidate
          let xCountInSuffix = Map.findWithDefault 0 x suffixVars

          guard $ (if rule == One then 0 else 1) == xCountInSuffix

          pure ((rule, l, r), replacement, prefix suffixGoals)
        suffixVars' = addVariables tVars suffixVars
        suffixGoals' = t : suffixGoals
      in
        validate rest suffixVars' suffixGoals' $ case valid of
          Just result -> result : confirmed
          Nothing -> confirmed

{- | Order the variable sides of a unification and the terms that substitute
for them.

If both sides are variables, the variable with fewer total occurrences is
preferred; if their counts are equal, the right-hand variable is preferred.
The other side is retained as a fallback when the preferred side cannot
satisfy an inlining rule.
-}
unificationCandidates
  :: Map String Int
  -- ^ Number of occurrences of each variable in the whole clause.
  -> Term
  -- ^ Left side of unification to select from.
  -> Term
  -- ^ Right side of unification to select from.
  -> [(String, Term)]
  -- ^ Possible selected variables and the terms that replace them.
unificationCandidates totalVars left right = pick (var left) (var right)
  where
    var (Var (VariableName _ name)) = Just name
    var _ = Nothing

    pick :: Maybe String -> Maybe String -> [(String, Term)]
    pick (Just l) (Just r)
      | Map.lookup l totalVars < Map.lookup r totalVars = [(l, right), (r, left)]
      | otherwise = [(r, left), (l, right)]
    pick (Just l) Nothing = [(l, right)]
    pick Nothing (Just r) = [(r, left)]
    pick Nothing Nothing = []

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
