module Prolog.Programming.CodeAnalysis.Rules.SingletonVariables (singletonVariablesChecker) where

import qualified Data.Map as Map (filter, keys)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), prettifyClause)
import Prolog.Programming.CodeAnalysis.Helper (countVariables)
import Prolog.Programming.CodeAnalysis.Types (ClauseRule, Problem (..))
import Text.PrettyPrint.Leijen.Text (indent, linebreak, string, vsep)

singletonVariablesChecker :: ClauseRule
singletonVariablesChecker (name, args, goals) = map (toProblem clause) singletonVariables
  where
    clause = Clause name args goals
    singletonVariables = Map.keys . Map.filter (== 1) $ countVariables clause

toProblem :: Clause -> String -> Problem
toProblem clause var =
  Problem {
    problemDisplay =
      vsep
        [ string $ pack "Your clause"
        , indent 2 $ string $ pack $ prettifyClause clause
        , string (pack $ "includes the singleton variable " ++ var ++ ".") <> linebreak
        , string $ pack "You can safely replace it with a wildcard (_)."
        ]
    }
