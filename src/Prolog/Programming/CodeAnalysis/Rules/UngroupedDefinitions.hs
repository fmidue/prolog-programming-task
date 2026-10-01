module Prolog.Programming.CodeAnalysis.Rules.UngroupedDefinitions (ungroupedDefinitionsChecker) where

import Data.List.Extra (anySame, groupOn)
import Data.List.Ordered (isSorted)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (Problem (..), ProgramRule)
import Text.PrettyPrint.Leijen.Text (string)

ungroupedDefinitionsChecker :: ProgramRule
ungroupedDefinitionsChecker clauses =
  [toProblem "Your code does not group predicate definitions by predicate name." | duplicateExists]
    ++ [ toProblem "Your code does not sort the predicate definitions ascending by arity (per group)."
       | not (all (isSorted . map snd) groupedByName)
       ]
  where
    groupedByName = groupOn fst $ map clauseIdentity clauses
    groupNames = map (fst . head) groupedByName
    duplicateExists = anySame groupNames

clauseIdentity :: Clause -> (String, Int)
clauseIdentity (Clause (Struct name args) _) = (name, length args)
clauseIdentity _ = error "This should never happen."

toProblem :: String -> Problem
toProblem msg =
  Problem {
    problemDisplay = string $ pack msg
    }
