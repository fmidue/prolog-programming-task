{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.SymbolOverload where

import Data.Foldable.Extra (notNull)
import Data.Generics (everything, mkQ)
import Data.List (singleton)
import Data.Set (Set)
import qualified Data.Set as Set (
  difference,
  empty,
  insert,
  intersection,
  singleton,
  toList,
  union,
  unions,
 )
import Data.Text.Lazy (pack)
import Language.Prolog (Atom, Goal, Term (Struct))
import Prolog.Programming.CodeAnalysis.Types (Context, Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (hcat, hsep, string, vcat)

symbolOverloadChecker :: Context -> ProgramRule
symbolOverloadChecker otherDefinitions prog
  | notNull (Set.intersection taskPredicates taskDataCons) =
      singleton
        $ Problem
        $ vcat
          [ "An unexpected error occurred."
          , "This is usually not caused by a fault within your submission."
          , "Please contact your lecturers, providing the following error message:"
          , "Task instance has mixed usage of predicates and data constructors under same name."
          ]
  | otherwise =
      concat
        [ toProblems (toTaskProblem "data constructor" "predicate") taskPredicatesAsSubmissionDataCons
        , toProblems (toTaskProblem "predicate" "data constructor") taskDataConsAsSubmissionPredicates
        , toProblems toSubmissionProblem
            $ Set.difference submissionIntersection
            $ Set.union taskDataConsAsSubmissionPredicates taskDataConsAsSubmissionPredicates
        ]
  where
    (taskPredicates, taskDataCons) =
      partitionIdentities
        $ Set.unions
        $ map grabPredicatesAndDataConstructorsFromClause otherDefinitions
    (submissionPredicates, submissionDataCons) =
      partitionIdentities
        $ Set.unions
        $ map grabPredicatesAndDataConstructorsFromClause prog

    taskPredicatesAsSubmissionDataCons = Set.intersection taskPredicates submissionDataCons
    taskDataConsAsSubmissionPredicates = Set.intersection taskDataCons submissionPredicates

    submissionIntersection = Set.intersection submissionPredicates submissionDataCons

    toProblems mapper s = map mapper $ Set.toList s

    partitionIdentities = foldr partition (Set.empty, Set.empty)
    partition (Left sig) (ps, ds) = (Set.insert sig ps, ds)
    partition (Right sig) (ps, ds) = (ps, Set.insert sig ds)

-- Left constructor is used for Predicates; Right for data constructors
grabPredicatesAndDataConstructorsFromClause :: (Atom, [Term], [Goal]) -> Set (Either Atom Atom)
grabPredicatesAndDataConstructorsFromClause (name, args, goals) =
  Set.union fromClauseHead $ Set.unions $ map grabPredicatesAndDataConstructors goals
  where
    fromClauseHead =
      Set.insert (Left name) $
        everything Set.union (mkQ Set.empty structToDataCons) args

grabPredicatesAndDataConstructors :: Term -> Set (Either Atom Atom)
grabPredicatesAndDataConstructors (Struct name args) =
  Set.insert (Left name) $ case (name, args) of
    (n, [arg]) | n `elem` ["\\+", "not"] -> grabPredicatesAndDataConstructors arg
    (n, [l, r])
      | n `elem` [";", ","] ->
          Set.union (grabPredicatesAndDataConstructors l) (grabPredicatesAndDataConstructors r)
    (_, args') -> everything Set.union (mkQ Set.empty structToDataCons) args'
grabPredicatesAndDataConstructors _ = Set.empty

structToDataCons :: Term -> Set (Either a Atom)
structToDataCons (Struct structName _) = Set.singleton $ Right structName
structToDataCons _ = Set.empty

toTaskProblem :: String -> String -> Atom -> Problem
toTaskProblem usedAs shouldBe name =
  Problem $
    hsep
      [ "Your program contains the symbol with name"
      , string $ pack $ show name
      , "which is used as a"
      , string $ pack usedAs
      , "but should really be used as a"
      , string $ pack shouldBe
      , "."
      ]

toSubmissionProblem :: Atom -> Problem
toSubmissionProblem name =
  Problem $
    hsep
      [ "Your program contains the symbol with name"
      , string $ pack $ show name
      , "which is used interchangeably as a predicate and a data constructor."
      ]
