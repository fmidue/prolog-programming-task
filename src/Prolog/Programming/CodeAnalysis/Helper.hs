module Prolog.Programming.CodeAnalysis.Helper where

import Data.Set (Set)
import qualified Data.Set as Set (empty, singleton, unions)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Predicate)

grabPredicateIdentities :: Term -> Set Predicate
grabPredicateIdentities (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      Set.unions $ map grabPredicateIdentities args
  | otherwise = Set.singleton (name, length args)
grabPredicateIdentities _ = Set.empty

grabIdentitiesInClause :: Bool -> Clause -> Set Predicate
grabIdentitiesInClause includeLhs (Clause ls rs) =
  Set.unions $ map grabPredicateIdentities $ if includeLhs then ls : rs else rs
grabIdentitiesInClause includeLhs (ClauseFn ls _) =
  if includeLhs
    then grabPredicateIdentities ls
    else Set.empty
