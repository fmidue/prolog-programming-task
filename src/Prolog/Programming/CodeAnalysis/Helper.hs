module Prolog.Programming.CodeAnalysis.Helper (clauseIdentities) where

import Data.List (find)
import Data.Set (Set)
import qualified Data.Set as Set (empty, insert, singleton, unions)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Predicate (..))

wrappers :: [Predicate]
wrappers =
  [ Predicate "," 2
  , Predicate ";" 2
  , Predicate "\\+" 1
  , Predicate "not" 1
  ]

-- | Return predicate information (name and arity) for left- and right-hand side of a program clause
clauseIdentities :: Bool -> Clause -> (Predicate, Set Predicate)
clauseIdentities includeWrapperPredicates (Clause (Struct name args) rs) =
  (Predicate name (length args), Set.unions $ map (grabPredicateIdentities includeWrapperPredicates) rs)
clauseIdentities _ _ = error "This should never be accessed."

grabPredicateIdentities :: Bool -> Term -> Set Predicate
grabPredicateIdentities includeWrapperPredicates (Struct name args) = case find ((== name) . predicateName) wrappers of
  Nothing -> Set.singleton $ Predicate name (length args)
  Just wrapper ->
    Set.insert wrapper
      $ Set.unions
      $ map (grabPredicateIdentities includeWrapperPredicates) args
grabPredicateIdentities _ _ = Set.empty
