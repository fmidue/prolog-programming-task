module Prolog.Programming.CodeAnalysis.Helper where

import Data.Set (Set)
import qualified Data.Set as Set (empty, singleton, unions)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Predicate)

clauseIdentity :: Clause -> Predicate
clauseIdentity (Clause (Struct name args) _) = (name, length args)
clauseIdentity _ = error "This should never happen."

grabPredicateIdentities :: Term -> Set Predicate
grabPredicateIdentities (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      Set.unions $ map grabPredicateIdentities args
  | otherwise = Set.singleton (name, length args)
grabPredicateIdentities _ = Set.empty

grabIdentitiesInClauseRhs :: Clause -> Set Predicate
grabIdentitiesInClauseRhs (Clause _ rs) =
  Set.unions $ map grabPredicateIdentities rs
grabIdentitiesInClauseRhs _ =
  Set.empty
