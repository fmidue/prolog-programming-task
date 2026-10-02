module Prolog.Programming.CodeAnalysis.Helper (clauseIdentities) where

import Data.Set (Set)
import qualified Data.Set as Set (empty, singleton, unions)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Predicate)

-- | Return predicate information (name and arity) for lhs and for all literals in rhs
clauseIdentities :: Clause -> (Predicate, Set Predicate)
clauseIdentities (Clause (Struct name args) rs) = ((name, length args), Set.unions $ map grabPredicateIdentities rs)
clauseIdentities _ = error "This should never be accessed."

grabPredicateIdentities :: Term -> Set Predicate
grabPredicateIdentities (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      Set.unions $ map grabPredicateIdentities args
  | otherwise = Set.singleton (name, length args)
grabPredicateIdentities _ = Set.empty
