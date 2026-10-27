module Prolog.Programming.CodeAnalysis.Rules.Inlining (inliningChecker) where

import Control.Applicative (asum)
import Data.Generics (listify)
import Data.Map (Map)
import qualified Data.Map as Map (
  differenceWith,
  disjoint,
  empty,
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
  prettifyClause,
  prettifyTerm,
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
    $ collectUnifications (countVariables args) goals
  where
    clause = Clause name args goals
    clauseHead = Struct name args

    fixedClause (x, term) =
      let
        sub = (VariableName 0 x, term)
        substitutedHead = substitute sub clauseHead
      in
        case substitutedHead of
          Struct newName newArgs -> Clause newName newArgs . map (substitute sub)
          _ -> error "should not happen"

{- | Collect unifications that can be inlined.

For each unification whose two sides have disjoint variables and which satisfies
one of the inlining rules, the result records the unification goal,
the selected variable and replacement term, and the goals
besides it.
-}
collectUnifications
  :: Map String Int
  -- ^ Number of occurrences of each variable in the clause head.
  -> [Term]
  -- ^ Goals in the clause's right-hand side.
  -> [(Term, (String, Term), [Term])]
  -- ^ Unifications together with the goals besides them.
collectUnifications headVars goals = go goals Map.empty True True (countVariables goals) id
  where
    go [] _ _ _ _ _ = []
    go (g : gs) prefixVars prefixHasOnlyUnifications onlyAllowedOccurrencesInPrefixOtherwise suffixVars addPrefix =
      case g of
        (Struct "=" [l, r]) -> case asum $ map checkMaybe $ unificationCandidates l r of
          Nothing -> restResult
          Just uc -> (g, uc, addPrefix gs) : restResult
        _ -> restResult
      where
        gVars = countVariables g

        newSuffixVars =
          Map.differenceWith
            (\x y -> let res = x - y in if res > 0 then Just res else Nothing)
            suffixVars
            gVars

        restResult =
          go
            gs
            (Map.unionWith (+) gVars prefixVars)
            newPrefixHasOnlyUnifications
            newOnlyAllowedOccurrencesInPrefixOtherwise
            newSuffixVars
            (addPrefix . (g :))

        newPrefixHasOnlyUnifications =
          prefixHasOnlyUnifications && case g of
            (Struct "=" _) -> True
            _ -> False

        newOnlyAllowedOccurrencesInPrefixOtherwise =
          onlyAllowedOccurrencesInPrefixOtherwise
            && Map.disjoint gVars headVars
            && not (containsCut g)
            && null (listify isDisjunction g)

        isDisjunction (Struct ";" _) = True
        isDisjunction _ = False

        checkMaybe uv
          | check uv = Just uv
          | otherwise = Nothing

        -- Rule 1: If, on the right-hand side of a clause, following at most literals in which neither X
        -- nor variables from term/Y appear and the variables in the prefix are disjoint to
        -- the variables in the head — or the literals themselves consist only of equalities in which X
        -- does not appear — there is something like X = term or X = Y or Y = X or term = X,
        -- and X appears exactly once in the head and appears neither in term nor in the rest of the
        -- right-hand side (and X and Y are different variables), then this equality may be inlined.

        -- Rule 2: If something like this appears somewhere on the right-hand side of a clause
        -- (not necessarily right at the beginning), and X does not appear in the head, nor in
        -- the initial part of the right-hand side up to this equation (and, of course, not in term/Y either),
        -- and if X appears exactly once in the remaining part of the right-hand side,
        -- then this equality may be inlined.

        check (v, t) =
          let
            tVars = countVariables t
            varNotInTerm = Map.notMember v tVars
            varNotInPrefix = Map.notMember v prefixVars
            maybeVarCountInHead = Map.lookup v headVars
            maybeVarCountInSuffix = Map.lookup v newSuffixVars

            rule1 =
              maybeVarCountInHead == Just 1
                && ( prefixHasOnlyUnifications
                       || (onlyAllowedOccurrencesInPrefixOtherwise && Map.disjoint tVars prefixVars)
                   )
                && isNothing maybeVarCountInSuffix

            rule2 =
              isNothing maybeVarCountInHead
                && maybeVarCountInSuffix == Just 1
          in
            varNotInTerm
              && varNotInPrefix
              && (rule1 || rule2)

{- | Give the variable sides of a unification and the terms that substitute
for them.
-}
unificationCandidates
  :: Term
  -- ^ Left side of unification to select from.
  -> Term
  -- ^ Right side of unification to select from.
  -> [(String, Term)]
  -- ^ Possible selected variables and the terms that replace them.
unificationCandidates left right = pair left right ++ pair right left
  where
    pair (Var (VariableName _ name)) other = [(name, other)]
    pair _ _ = []

toProblem :: Clause -> Term -> Clause -> Problem
toProblem originalClause equality fixedClause =
  Problem {
    problemDisplay =
      vsep
        [ string $ pack "Your clause"
        , indent 2 $ string $ pack $ prettifyClause originalClause
        , string $ pack "uses the unification"
        , indent 2 $ string $ pack $ prettifyTerm equality
        , string $ pack "as a goal that can also directly be applied to the clause."
        , string $ pack "Doing that would result in:"
        , indent 2 $ string $ pack $ prettifyClause fixedClause
        ]
    }
