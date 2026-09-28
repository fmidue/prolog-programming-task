module CodeAnalysis.Helper where

import Language.Prolog (consultString)
import Prolog.Programming.CodeAnalysis (checkForProblems)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  Problem (problemDisplay),
  WithSeverity (..),
 )
import Test.HUnit (assertFailure)
import Test.Hspec (Expectation)

shouldDetectProblemsStrict :: CodeAnalysisConfig -> [String -> Bool] -> String -> Expectation
shouldDetectProblemsStrict cfg pts code = case consultString code of
  Left err -> assertFailure $ "Failed to parse prolog program:\n" ++ show err
  Right prog -> case checkForProblems cfg prog [] of
    [] -> assertFailure "No problems found"
    pbs
      | length pbs /= length pts ->
          assertFailure $ "Found " ++ show (length pbs) ++ " instead of " ++ show (length pts) ++ " problems."
      | all (\t -> any (t . show . problemDisplay . value) pbs) pts -> pure ()
      | otherwise -> assertFailure "Found problems that does not match"

shouldNotHaveProblems :: CodeAnalysisConfig -> String -> Expectation
shouldNotHaveProblems cfg code = case consultString code of
  Left err -> assertFailure $ "Failed to parse prolog program:\n" ++ show err
  Right prog -> case checkForProblems cfg prog [] of
    [] -> pure ()
    _ -> assertFailure "Detected problem(s) even though they should not exist."
