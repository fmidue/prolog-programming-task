{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.ConsistentArity (consistentArityRule) where

import Data.Generics (everything, mkQ)
import Data.List.Extra (groupSort, nubOrd)
import Data.Text.Lazy (pack)
import Language.Prolog (Term (..))
import Prolog.Programming.CodeAnalysis.Types (IgnoredPredicates (IgnoredPredicates), Problem (..), Rule (ProgramRule))
import Text.PrettyPrint.Leijen.Text (string)

consistentArityRule :: IgnoredPredicates -> Rule
consistentArityRule (IgnoredPredicates ignore) = ProgramRule $ \clauses ->
  let
    identities = everything (++) (mkQ [] grabIdentity) clauses
    groupedByName = groupSort identities
    predicatesWithMultipleArities = filter ((> 1) . length . nubOrd . snd) groupedByName
  in
    [toProblem name | (name, _) <- predicatesWithMultipleArities, name `notElem` ignore]

grabIdentity :: Term -> [(String, Int)]
grabIdentity (Struct name args) = [(name, length args)]
grabIdentity _ = []

toProblem :: String -> Problem
toProblem name =
  Problem {
    problemDisplay =
      string
        $ pack
        $ "Your program contains the predicate/functor " ++ name ++ " which is used/defined with different arities."
    }
