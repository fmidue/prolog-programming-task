module Prolog.Programming.CodeAnalysis.Helper (clauseIdentities) where

import Data.Set (Set)
import qualified Data.Set as Set (empty, insert, singleton, unions)
import Language.Prolog (Atom, Goal, Signature (Signature), Term (..))

-- | Return predicate information (name and arity) for left- and right-hand side of a program clause
clauseIdentities :: Bool -> (Atom, [Term], [Goal]) -> (Signature, Set Signature)
clauseIdentities includeWrapperPredicates (name, args, rs) =
  (Signature name (length args), Set.unions $ map (grabPredicateIdentities includeWrapperPredicates) rs)

grabPredicateIdentities :: Bool -> Term -> Set Signature
grabPredicateIdentities includeWrapperPredicates (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      (if includeWrapperPredicates then Set.insert (Signature name (length args)) else id)
        $ Set.unions
        $ map (grabPredicateIdentities includeWrapperPredicates) args
  | otherwise = Set.singleton $ Signature name (length args)
grabPredicateIdentities _ _ = Set.empty
