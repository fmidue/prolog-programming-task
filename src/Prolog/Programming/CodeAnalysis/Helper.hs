{-# LANGUAGE LambdaCase #-}

module Prolog.Programming.CodeAnalysis.Helper (
  clauseIdentities,
  countVariables,
  containsCut,
) where

import Data.Data (Data)
import Data.Generics (everything, mkQ)
import Data.Map (Map)
import qualified Data.Map as Map (empty, singleton, unionWith)
import Data.Set (Set)
import qualified Data.Set as Set (empty, insert, singleton, unions)
import Language.Prolog (Clause (..), Term (..), VariableName (..))
import Prolog.Programming.CodeAnalysis.Types (Predicate (..))

-- | Return predicate information (name and arity) for left- and right-hand side of a program clause
clauseIdentities :: Bool -> Clause -> (Predicate, Set Predicate)
clauseIdentities includeWrapperPredicates (Clause (Struct name args) rs) =
  (Predicate name (length args), Set.unions $ map (grabPredicateIdentities includeWrapperPredicates) rs)
clauseIdentities _ _ = error "This should never be accessed."

grabPredicateIdentities :: Bool -> Term -> Set Predicate
grabPredicateIdentities includeWrapperPredicates (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      (if includeWrapperPredicates then Set.insert (Predicate name (length args)) else id)
        $ Set.unions
        $ map (grabPredicateIdentities includeWrapperPredicates) args
  | otherwise = Set.singleton $ Predicate name (length args)
grabPredicateIdentities _ _ = Set.empty

-- | Return variables and their amount of occurrences in the given structure
countVariables :: Data a => a -> Map String Int
countVariables = everything (Map.unionWith (+)) $ mkQ Map.empty count
  where
    count :: Term -> Map String Int
    count (Var (VariableName _ name)) = Map.singleton name 1
    count _ = Map.empty

-- | Check whether a term in the structure represents the cut operator
containsCut :: Data a => a -> Bool
containsCut = everything (||) $ mkQ False $ \case
  Cut _ -> True
  _ -> False
