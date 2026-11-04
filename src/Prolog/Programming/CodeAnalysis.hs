{-# LANGUAGE RecordWildCards #-}

module Prolog.Programming.CodeAnalysis (
  checkForProblems,
  displayProblems,
)
where

import Data.Text.Lazy (pack)
import Language.Prolog (ProgramClause)
import Prolog.Programming.CodeAnalysis.Config (configuredRules)
import Prolog.Programming.CodeAnalysis.Types (
  CheckStage,
  CodeAnalysisConfig (..),
  Context,
  Problem (..),
  Severity (Error),
  WithSeverity (..),
 )
import Text.PrettyPrint.Leijen.Text (Doc, brackets, string, vsep, (<$$>))

checkForProblems :: CheckStage -> CodeAnalysisConfig -> [ProgramClause] -> Context -> [WithSeverity Problem]
checkForProblems stage cfg program = concatMap (traverse ($ program)) . configuredRules stage cfg

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
