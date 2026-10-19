module Prolog.Programming.CodeAnalysis.Rules.Inlining (inliningChecker) where

import Control.Applicative (asum)
import Data.Generics (listify)
import Data.List.Extra (notNull)
import Data.Map (Map)
import qualified Data.Map as Map (
  disjoint,
  empty,
  findWithDefault,
  lookup,
  notMember,
  unionWith,
 )
import Data.Maybe (isNothing)
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
    ( \(u, replacement, goals') ->
        toProblem clause u $ fixedClause replacement goals'
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

{- | Collect unifications that can be inlined.

For each unification whose two sides have disjoint variables and which satisfies
one of the inlining rules, the result records the unification goal,
the selected variable and replacement term, and the goals
besides it.
-}
collectUnifications
  :: Map String Int
  -- ^ Number of occurrences of each variable in the whole clause.
  -> Map String Int
  -- ^ Number of occurrences of each variable in the clause head.
  -> [Term]
  -- ^ Goals in the clause's right-hand side.
  -> [(Term, (String, Term), [Term])]
  -- ^ Unifications together with the goals besides them.
collectUnifications totalVars headVars goals = go goals Map.empty True False id
  where
    go [] _ _ _ _ = []
    go (g : gs) prefixVars prefixHasOnlyUnifications disallowedOpInPrefix addPrefix = case g of
      (Struct "=" [l, r]) -> case asum $ map checkMaybe $ unificationCandidates totalVars l r of
        Nothing -> restResult
        Just uc -> (g, uc, addPrefix gs) : restResult
      _ -> restResult
      where
        gVars = countVariables g
        restResult =
          go
            gs
            (Map.unionWith (+) gVars prefixVars)
            newPrefixHasOnlyUnifications
            newDisallowedOpInPrefix
            (addPrefix . (g :))

        suffixCount x =
          Map.findWithDefault 0 x totalVars
            - Map.findWithDefault 0 x headVars
            - Map.findWithDefault 0 x prefixVars
            - Map.findWithDefault 0 x gVars

        newDisallowedOpInPrefix = disallowedOpInPrefix || containsCut g || containsDisjunction g
        newPrefixHasOnlyUnifications =
          prefixHasOnlyUnifications && case g of
            (Struct "=" _) -> True
            _ -> False

        containsDisjunction = notNull . listify isDisjunction

        isDisjunction (Struct ";" _) = True
        isDisjunction _ = False

        checkMaybe uv
          | check uv = Just uv
          | otherwise = Nothing

        -- Regel 1: Wenn auf der rechten Seite einer Klausel nach höchstens Literalen, in denen weder X
        -- noch Variablen aus term/Y vorkommen oder ihrerseits nur aus Gleichheiten bestehen,
        -- in denen X aber nicht vorkommt, etwas wie X = term oder X = Y oder Y = X oder term = X steht,
        -- und X im Head genau einmal und weder in term noch im Rest der rechten Seite vorkommt
        -- (und X und Y verschiedene Variablen sind), dann darf diese Gleichheit weggelassen
        -- und X im Head entsprechend ersetzt werden.

        -- Regel 2: Wenn auf der rechten Seite einer Klausel irgendwo (nicht unbedingt direkt am Anfang)
        -- so etwas auftritt und X weder im Head, noch im Anfangsstück der rechten Seite bis zu dieser Gleichung
        -- (und natürlich auch wieder nicht in term/Y) vorkommt,
        -- und danach im Reststück der rechten Seite X nur genau einmal vorkommt, dann darf wieder diese Gleichheit
        -- weggelassen und X an der entsprechenden Stelle ersetzt werden.

        check (v, t) =
          let
            varNotInTerm = Map.notMember v (countVariables t)
            varNotInPrefix = Map.notMember v prefixVars
            vInHead = Map.lookup v headVars
            vCountInSuffix = suffixCount v

            rule1 =
              ( (prefixHasOnlyUnifications && varNotInPrefix)
                  || (not disallowedOpInPrefix && Map.disjoint gVars prefixVars)
              )
                && vInHead == Just 1
                && vCountInSuffix == 0

            rule2 =
              isNothing vInHead
                && varNotInPrefix
                && vCountInSuffix == 1
          in
            varNotInTerm
              && (rule1 || rule2)

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
