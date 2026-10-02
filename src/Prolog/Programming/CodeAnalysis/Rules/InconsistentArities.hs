{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.InconsistentArities (inconsistentAritiesChecker) where

import Data.Bifunctor (second)
import Data.List.Extra (groupSort)
import Data.Map (Map)
import qualified Data.Map as Map (fromList, lookup)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set (insert, toList, unions)
import Data.Text.Lazy (pack)
import Prolog.Programming.CodeAnalysis.Helper (clauseIdentity, grabIdentitiesInClauseRhs)
import Prolog.Programming.CodeAnalysis.Types (Context, IgnoredPredicates (..), Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string, vcat)

inconsistentAritiesChecker :: Context -> IgnoredPredicates -> ProgramRule
inconsistentAritiesChecker otherDefinitions (IgnoredPredicates ignore) clauses =
  case forcedIdentities ignore (identities otherDefinitions) of
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
        $ filter
          (\(n, _) -> n `notElem` ignore)
        $ identities clauses
  where
    identities = groupSort . Set.toList . Set.unions . map (\c -> Set.insert (clauseIdentity c) (grabIdentitiesInClauseRhs c))

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

forcedIdentities :: [String] -> [(String, [Int])] -> Maybe (Map String Int)
forcedIdentities ignore identities
  | any inconsistent identities = Nothing
  | otherwise = Just $ Map.fromList $ map (second head) identities
  where
    inconsistent (name, arities) =
      length arities > 1 && name `notElem` ignore

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
