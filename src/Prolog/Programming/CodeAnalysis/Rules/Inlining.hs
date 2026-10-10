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
      Clause (apply [sub] clauseHead) $ map (apply [sub]) rhs
inliningChecker _ = []

collectInformation
  :: [Term]
  -> Map String Int
  -> [Term]
  -> [(Term, Map String Int, Map String Int, [Term])]
  -> [(Term, Map String Int, Map String Int, [Term])]
collectInformation [] _ _ us = us
collectInformation (t : ts) vs goals us =
  collectInformation ts (addVarsFromT vs) (goals ++ [t]) newUs
  where
    addVarsFromT = Map.unionWith (+) (countVariables t)
    newUs =
      map (\(t', p, s, goals') -> (t', p, addVarsFromT s, goals' ++ [t])) us ++ case t of
        Struct "=" [l, r]
          | Map.disjoint (countVariables l) (countVariables r) ->
              [(t, vs, Map.empty, goals)]
        _ -> []

unification :: Map String Int -> Term -> (String, Term)
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

checkApplicable
  :: Map String Int
  -> Map String Int
  -> (Term, Map String Int, Map String Int, [Term])
  -> Maybe Substitution
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
