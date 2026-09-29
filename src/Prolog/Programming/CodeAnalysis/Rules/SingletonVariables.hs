module Prolog.Programming.CodeAnalysis.Rules.SingletonVariables (singletonVariablesChecker) where

import Data.Generics (Data, everything, mkQ)
import Data.Map (Map)
import qualified Data.Map as Map (empty, filter, keys, singleton, unionWith)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..), VariableName (..))
import Prolog.Programming.CodeAnalysis.Types (ClauseRule, Problem (..))
import Text.PrettyPrint.Leijen.Text (indent, linebreak, string, vsep)

singletonVariablesChecker :: ClauseRule
singletonVariablesChecker clause = map (toProblem clause) singletonVariables
  where
    singletonVariables = Map.keys . Map.filter (== 1) $ countVariables clause

countVariables :: Data a => a -> Map String Int
countVariables = everything (Map.unionWith (+)) $ mkQ Map.empty count
  where
    count :: Term -> Map String Int
    count (Var (VariableName _ name)) = Map.singleton name 1
    count _ = Map.empty

toProblem :: Clause -> String -> Problem
toProblem clause var =
  Problem {
    problemDisplay =
      vsep
        [ string $ pack "Your clause"
        , indent 2 $ string $ pack $ show clause
        , string (pack $ "includes the singleton variable " ++ var ++ ".") <> linebreak
        , string $ pack "You can safely replace it with a wildcard (_)."
        ]
    }
