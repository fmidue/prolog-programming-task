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
import Language.Prolog (Atom, Goal, Signature (Signature), Term (..), VariableName (..))

-- | Return predicate information (name and arity) for left- and right-hand side of a program clause
clauseIdentities :: Bool -> (Atom, [Term], [Goal]) -> (Signature, Set Signature)
clauseIdentities includeWrapperPredicates (name, args, rs) =
  (Signature name (length args), Set.unions $ map (grabPredicateIdentities includeWrapperPredicates) rs)

grabPredicateIdentities :: Bool -> Term -> Set Signature
grabPredicateIdentities includeWrapperPredicates (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      (if includeWrapperPredicates then Set.insert sig else id)
        $ Set.unions
        $ map (grabPredicateIdentities includeWrapperPredicates) args
  | otherwise = Set.singleton sig
  where
    sig = Signature name (length args)
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
