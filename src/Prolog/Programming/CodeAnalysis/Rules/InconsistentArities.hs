{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.InconsistentArities (inconsistentAritiesChecker) where

import Control.Monad (foldM)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE (groupWith, head, map)
import Data.Map (Map)
import qualified Data.Map as Map (empty, insert, lookup)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set (filter, insert, unions)
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
        $ identities clauses
  where
    identities =
      map
        (\group -> (fst (NE.head group), NE.map snd group))
        . NE.groupWith fst
        . Set.unions
        . map (Set.filter ((`notElem` ignore) . fst) . uncurry Set.insert . clauseIdentities)

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
forcedIdentities = foldM addIdentity Map.empty
  where
    addIdentity forced (name, arities) =
      case arities of
        arity :| [] -> Just $ Map.insert name arity forced
        _ -> Nothing

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
