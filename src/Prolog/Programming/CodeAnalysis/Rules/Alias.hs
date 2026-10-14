{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.Alias (aliasChecker) where

import Data.List.Extra (nubOrdOn)
import qualified Data.Map as Map (elems, fromListWith)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Helper (clauseIdentities)
import Prolog.Programming.CodeAnalysis.Types (
  Problem (..),
  ProgramRule,
 )
import Text.PrettyPrint.Leijen.Text (string, vcat)

aliasChecker :: ProgramRule
aliasChecker clauses = concatMap checkGroup partitionedByName
  where
    deduped = nubOrdOn show clauses
    partitionedByName =
      Map.elems
        $ Map.fromListWith (++)
        $ map (\c -> (fst $ clauseIdentities False c, [c])) deduped

checkGroup :: [Clause] -> [Problem]
checkGroup [Clause (Struct alias args1) [Struct aliased args2]] =
  [toProblem alias aliased | alias /= aliased, args1 == args2]
checkGroup _ = []

toProblem :: String -> String -> Problem
toProblem alias aliased =
  Problem {
    problemDisplay =
      vcat
        [ string $ pack $ "It looks like you renamed predicate " ++ aliased ++ " using an alias."
        , string $ pack $ "Why don't you use the name " ++ alias ++ " directly?"
        ]
    }
