{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ConfigSpec where

import Control.Exception (IOException, try)
import Data.Either.Extra (mapLeft)
import Data.List (isInfixOf, isPrefixOf)
import Prolog.Programming.Data (Config)
import Prolog.Programming.Task (exampleConfig, verifyConfig)
import Test.Hspec (Spec, describe, it, shouldReturn, shouldSatisfy)

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
