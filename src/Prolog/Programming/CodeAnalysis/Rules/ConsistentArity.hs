{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.ConsistentArity (consistentArityRule) where

import Data.List.Extra (groupSort, nubOrd)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (IgnoredPredicates (IgnoredPredicates), Problem (..), Rule (ProgramRule))
import Text.PrettyPrint.Leijen.Text (string)

consistentArityRule :: IgnoredPredicates -> Rule
consistentArityRule (IgnoredPredicates ignore) = ProgramRule $ \clauses _ ->
  let
    identities = concatMap identitiesInClause clauses
    groupedByName = groupSort identities
    predicatesWithMultipleArities = filter ((> 1) . length . nubOrd . snd) groupedByName
  in
    [toProblem name | (name, _) <- predicatesWithMultipleArities, name `notElem` ignore]

identitiesInClause :: Clause -> [(String, Int)]
identitiesInClause (Clause ls rs) = concatMap grabIdentity $ ls : rs
identitiesInClause (ClauseFn ls _) = grabIdentity ls

grabIdentity :: Term -> [(String, Int)]
grabIdentity (Struct name args) = case name of
  "," -> concatMap grabIdentity args
  ";" -> concatMap grabIdentity args
  _ -> [(name, length args)]
grabIdentity _ = []

toProblem :: String -> Problem
toProblem name =
  Problem {
    problemDisplay =
      string
        $ pack
        $ "Your program contains the predicate " ++ name ++ " which is used/defined with different arities."
    }
