module CodeAnalysis.Rules.AliasSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  AliasConfig (..),
  CodeAnalysisConfig (..),
  Severity (..),
  WithSeverity (..),
 )
import Prolog.Programming.Data (Code)
import Test.Hspec (Spec, describe, it)

caConfig :: CodeAnalysisConfig
caConfig =
  emptyCodeAnalysisConfig {
    alias = AliasConfig $ Just $ WithSeverity Hint ()
    }

withAlias :: [(Code, String, String)]
withAlias =
  [ ("betterName(X) :- badName(X).", "betterName", "badName")
  ]

detectionFree :: [Code]
detectionFree =
  [ "a(X) :- b(Y)."
  , "a(X) :- b(X). a(a)."
  , "a(X) :- b(X), c(X)."
  , "a(X) :- b(X). b(_). a(X) :- a(X)."
  ]

spec :: Spec
spec = describe "Alias" $ do
  describe "Should detect predicate aliases" $
    forM_ withAlias $ \(programCode, aliasName, originalName) ->
      it programCode $
        shouldDetectProblemsStrict
          caConfig
          [ \problem ->
              isInfixOf ("renamed predicate " ++ originalName ++ " using an alias") problem
                && isInfixOf ("use the name " ++ aliasName ++ " directly") problem
          ]
          programCode
  describe "Should not detect any problems" $ do
    forM_ detectionFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems caConfig programCode
