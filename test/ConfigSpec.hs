{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ConfigSpec where

import Control.Exception (IOException, try)
import Data.Either.Extra (mapLeft)
import Data.List (isInfixOf, isPrefixOf)
import Prolog.Programming.CodeAnalysis.Types (
  CheckStage (..),
  CodeAnalysisConfig (..),
  InliningConfig (..),
  RedundantCodeConfig (..),
  Severity (..),
  SymbolOverloadConfig (..),
  WithSeverity (WithSeverity),
 )
import Prolog.Programming.Data (Config)
import Prolog.Programming.Task (exampleConfig, toInstance, verifyConfig)
import Prolog.Programming.Types (codeAnalysis, taskConfig)
import Test.Hspec (Spec, describe, it, shouldReturn, shouldSatisfy)
import qualified Text.RawString.QQ as RS (r)

evaluateVerify :: Config -> IO (Either String ())
evaluateVerify config = do
  result <- try (verifyConfig config) :: IO (Either IOException ())

  pure $ mapLeft show result

withoutConfigPart :: Config
withoutConfigPart = "\n" ++ unlines (dropWhile (not . isPrefixOf "---") $ lines exampleConfig)

spec :: Spec
spec = describe "ExampleConfig" $ do
  it "example config should be valid" $
    evaluateVerify exampleConfig `shouldReturn` Right ()
  it "rejects config with unknown fields" $ do
    result <-
      evaluateVerify $ "globalTiimeout: 10000" ++ withoutConfigPart -- no-spell-check
    result `shouldSatisfy` \case
      Right () -> False
      Left msg -> "Unknown or forbidden fields: globalTiimeout" `isInfixOf` msg -- no-spell-check
  it "rejects config with negative globalTimeout" $ do
    result <-
      evaluateVerify $ "globalTimeout: -10000" ++ withoutConfigPart
    result `shouldSatisfy` \case
      Right () -> False
      Left msg -> "globalTimeout must be non-negative" `isInfixOf` msg
  it "rejects code analysis configs with stage set to 'before-tests' and status unlike 'reject'" $ do
    result <-
      evaluateVerify $
        [RS.r|
codeAnalysis:
  symbolOverload:
    status: hint
    stage: before-tests
      |]
          ++ withoutConfigPart
    result `shouldSatisfy` \case
      Right () -> False
      Left msg -> "Code analysis configs using the 'before-tests' stage must use the 'reject' status" `isInfixOf` msg
  it "doesn't allow to set the stage for 'redundantCode'" $ do
    result <-
      evaluateVerify $
        [RS.r|
codeAnalysis:
  redundantCode:
    status: reject
    stage: before-tests
      |]
          ++ withoutConfigPart
    result `shouldSatisfy` \case
      Right () -> False
      Left msg -> "Unknown or forbidden fields: stage" `isInfixOf` msg
  it "parses stages correctly" $ do
    let config =
          [RS.r|
rigorousValidation: false

codeAnalysis:
  redundantCode:
    status: warn
  symbolOverload:
    status: reject
    stage: before-tests
  inlining:
    status: hint
    stage: after-tests
      |]
            ++ withoutConfigPart
    result <- evaluateVerify config

    result `shouldSatisfy` \case
      Left _ -> False
      Right () -> case codeAnalysis $ taskConfig $ toInstance config of
        CodeAnalysisConfig {
          redundantCode = RedundantCodeConfig (Just (WithSeverity Warn (), AfterTests))
          , symbolOverload = SymbolOverloadConfig (Just (WithSeverity Error (), BeforeTests))
          , inlining = InliningConfig (Just (WithSeverity Hint (), AfterTests))
          } -> True
        _ -> False
