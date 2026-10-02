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
shouldDetectProblemsStrict cfg pts code = shouldDetectProblemsStrict' cfg pts code ""

shouldDetectProblemsStrict' :: CodeAnalysisConfig -> [String -> Bool] -> String -> String -> Expectation
shouldDetectProblemsStrict' cfg pts code other = case consultString code of
  Left err -> assertFailure $ "Failed to parse prolog program:\n" ++ show err
  Right prog -> case consultString other of
    Left err -> assertFailure $ "Failed to parse other definitions:\n " ++ show err
    Right otherDefs -> case checkForProblems cfg prog otherDefs of
      [] -> assertFailure "No problems found"
      pbs
        | length pbs /= length pts ->
            assertFailure $ "Found " ++ show (length pbs) ++ " instead of " ++ show (length pts) ++ " problems."
        | all (\t -> any (t . show . problemDisplay . value) pbs) pts -> pure ()
        | otherwise -> assertFailure "Found problems that does not match"

shouldNotHaveProblems :: CodeAnalysisConfig -> String -> Expectation
shouldNotHaveProblems cfg code = shouldNotHaveProblems' cfg code ""

shouldNotHaveProblems' :: CodeAnalysisConfig -> String -> String -> Expectation
shouldNotHaveProblems' cfg code other = case consultString code of
  Left err -> assertFailure $ "Failed to parse prolog program:\n" ++ show err
  Right prog -> case consultString other of
    Left err -> assertFailure $ "Failed to parse other definitions:\n " ++ show err
    Right otherDefs ->
      case checkForProblems cfg prog otherDefs of
        [] -> pure ()
        _ -> assertFailure "Detected problem(s) even though they should not exist."
