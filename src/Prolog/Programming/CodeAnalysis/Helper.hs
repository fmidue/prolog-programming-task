module Prolog.Programming.CodeAnalysis.Helper where

import Data.Set (Set)
import qualified Data.Set as Set (empty, singleton, unions)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Predicate (..))

clauseIdentities :: Clause -> (Predicate, Set Predicate)
clauseIdentities (Clause (Struct name args) rs) =
  (Predicate name (length args), Set.unions $ map grabPredicateIdentities rs)
clauseIdentities _ = error "This should never be accessed."

grabPredicateIdentities :: Term -> Set Predicate
grabPredicateIdentities (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      Set.unions $ map grabPredicateIdentities args
  | otherwise = Set.singleton $ Predicate name (length args)
grabPredicateIdentities _ = Set.empty
