module Prolog.Programming.CodeAnalysis.Helper (clauseIdentities) where

import Data.Set (Set)
import qualified Data.Set as Set (empty, insert, singleton, unions)
import Language.Prolog (Atom, Goal, Term (..))
import Prolog.Programming.CodeAnalysis.Types (Predicate (..))

-- | Return predicate information (name and arity) for left- and right-hand side of a program clause
clauseIdentities :: Bool -> (Atom, [Term], [Goal]) -> (Predicate, Set Predicate)
clauseIdentities includeWrapperPredicates (name, args, rs) =
  (Predicate name (length args), Set.unions $ map (grabPredicateIdentities includeWrapperPredicates) rs)

grabPredicateIdentities :: Bool -> Term -> Set Predicate
grabPredicateIdentities includeWrapperPredicates (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      (if includeWrapperPredicates then Set.insert (Predicate name (length args)) else id)
        $ Set.unions
        $ map (grabPredicateIdentities includeWrapperPredicates) args
  | otherwise = Set.singleton $ Predicate name (length args)
grabPredicateIdentities _ _ = Set.empty
