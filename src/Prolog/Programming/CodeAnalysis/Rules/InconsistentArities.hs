{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.InconsistentArities (inconsistentAritiesChecker) where

import Data.Bifunctor (second)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE (groupWith, head, length, map)
import Data.Map (Map)
import qualified Data.Map as Map (fromList, lookup)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set (filter, insert, toList, unions)
import Data.Text.Lazy (pack)
import Prolog.Programming.CodeAnalysis.Helper (clauseIdentities)
import Prolog.Programming.CodeAnalysis.Types (Context, IgnoredPredicates (..), Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string, vcat)

inconsistentAritiesChecker :: Context -> IgnoredPredicates -> ProgramRule
inconsistentAritiesChecker otherDefinitions (IgnoredPredicates ignore) clauses =
  case forcedIdentities (identities otherDefinitions) of
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
    identities =
      map
        (\group -> (fst (NE.head group), NE.map snd group))
        . NE.groupWith fst
        . Set.toList
        . Set.filter ((`notElem` ignore) . fst)
        . Set.unions
        . map (uncurry Set.insert . clauseIdentities)

data Result = MultipleArities String | InconsistentWithForced String Int

compareWithForced :: Map String Int -> (String, NonEmpty Int) -> Maybe Result
compareWithForced forced (name, arities) =
  case arities of
    arity :| [] ->
      case Map.lookup name forced of
        Just expected
          | expected /= arity ->
              Just $ InconsistentWithForced name expected
        _ -> Nothing
    _ -> Just $ MultipleArities name

forcedIdentities :: [(String, NonEmpty Int)] -> Maybe (Map String Int)
forcedIdentities identities
  | any inconsistent identities = Nothing
  | otherwise = Just $ Map.fromList $ map (second NE.head) identities
  where
    inconsistent (_, arities) =
      NE.length arities > 1

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
