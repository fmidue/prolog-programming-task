module Prolog.Programming.CodeAnalysis.Helper where

import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Predicate)

grabPredicateIdentities :: Term -> [Predicate]
grabPredicateIdentities (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      concatMap grabPredicateIdentities args
  | otherwise = [(name, length args)]
grabPredicateIdentities _ = []

grabIdentitiesInClause :: Bool -> Clause -> [Predicate]
grabIdentitiesInClause includeLhs (Clause ls rs) =
  concatMap grabPredicateIdentities $ if includeLhs then ls : rs else rs
grabIdentitiesInClause includeLhs (ClauseFn ls _) = if includeLhs then grabPredicateIdentities ls else []
