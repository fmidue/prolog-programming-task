{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Prolog.Programming.CodeAnalysis (
  checkForProblems,
  displayProblems,
)
where

import Data.List.Extra (partition)
import Data.Text.Lazy (pack)
import Language.Prolog (Program)
import Prolog.Programming.CodeAnalysis.Config (configuredRules)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  Problem (..),
  Rule (..),
  Severity (Error),
  WithSeverity (..),
 )
import Text.PrettyPrint.Leijen.Text (Doc, brackets, string, vsep, (<$$>))

checkForProblems :: CodeAnalysisConfig -> Program -> [WithSeverity Problem]
checkForProblems cfg prog =
  concatMap (\c -> concatMap (traverse (`clauseRule` c)) clauseRules) prog
    ++ concatMap (traverse (`programRule` prog)) programRules
  where
    (clauseRules, programRules) =
      partition
        (\case (WithSeverity _ (ClauseRule _)) -> True; _ -> False)
        $ configuredRules cfg

displayProblems :: [WithSeverity Problem] -> Either Doc Doc
displayProblems pbs =
  cons
    $ vsep
    $ map
      ( \WithSeverity {..} ->
          padEnd 30 "-" (brackets $ string $ pack $ show severity) <$$> problemDisplay value
      )
      pbs
  where
    cons = if any ((== Error) . severity) pbs then Left else Right

padEnd :: Int -> String -> Doc -> Doc
padEnd maxWidth filler x = x <> mconcat (replicate (max 0 (maxWidth - width x)) $ string $ pack filler)

width :: Doc -> Int
width doc = length $ show doc
