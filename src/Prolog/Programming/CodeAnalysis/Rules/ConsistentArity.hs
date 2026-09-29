{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.ConsistentArity (consistentArityChecker) where

import Data.Bifunctor (second)
import Data.List.Extra (groupSort, nubOrd)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Context, IgnoredPredicates (..), Problem (..), Rule (..))
import Text.PrettyPrint.Leijen.Text (string, vcat)

consistentArityChecker :: Context -> IgnoredPredicates -> Rule
consistentArityChecker otherDefinitions (IgnoredPredicates ignore) = ProgramRule $ \clauses ->
  case forcedIdentities otherDefinitions of
    Nothing ->
      [ Problem $
          vcat
            [ "An unexpected error occurred."
            , "This is usually not caused by a fault within your submission."
            , "Please contact your lecturers, providing the following error message:"
            , "Task instance does not satisfy arity constraint."
            ]
      ]
    Just forced ->
      mapMaybe
        (fmap toProblem . compareWithForced forced)
        $ filter (\(n, _) -> n `notElem` ignore)
        $ groupSort
        $ nubOrd
        $ concatMap identitiesInClause clauses

data Result = MultipleArities String | InconsistentWithForced String Int

compareWithForced :: Map String Int -> (String, [Int]) -> Maybe Result
compareWithForced forced (name, arities) =
  case arities of
    [] -> Nothing
    [_] ->
      case Map.lookup name forced of
        Just expected
          | expected /= head arities ->
              Just $ InconsistentWithForced name expected
        _ -> Nothing
    _ -> Just $ MultipleArities name

forcedIdentities :: [Clause] -> Maybe (Map String Int)
forcedIdentities clauses
  | any inconsistent identities = Nothing
  | otherwise = Just $ Map.fromList $ map (second head) identities
  where
    identities = groupSort $ concatMap identitiesInClause clauses

    inconsistent (_, arities) =
      length (nubOrd arities) > 1

identitiesInClause :: Clause -> [(String, Int)]
identitiesInClause (Clause ls rs) = concatMap grabIdentity $ ls : rs
identitiesInClause (ClauseFn ls _) = grabIdentity ls

grabIdentity :: Term -> [(String, Int)]
grabIdentity (Struct name args)
  | name `elem` [",", ";", "\\+", "not"] =
      (name, length args) : concatMap grabIdentity args
  | otherwise = [(name, length args)]
grabIdentity _ = []

toProblem :: Result -> Problem
toProblem res =
  Problem {
    problemDisplay =
      string $
        pack $
          case res of
            MultipleArities name ->
              "Your program contains the predicate " ++ name ++ " which is used/defined with different arities."
            InconsistentWithForced name correctArity ->
              "Your program contains the predicate "
                ++ name
                ++ " which is used/defined with wrong arity. It should be "
                ++ name
                ++ "/"
                ++ show correctArity
                ++ "."
    }
