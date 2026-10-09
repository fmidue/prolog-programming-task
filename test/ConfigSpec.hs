{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ConfigSpec where

import Control.Exception (SomeException, try)
import qualified Data.Text as T (pack, replace, unpack)
import Prolog.Programming.Data (Config)
import Prolog.Programming.Task (exampleConfig, verifyConfig)
import Test.Hspec (Spec, describe, it, shouldReturn)

doesNotThrow :: forall a. IO a -> IO Bool
doesNotThrow action = do
  result <- try action :: IO (Either SomeException a)
  pure $ case result of
    Left _ -> False
    Right _ -> True

invalidConfig :: Config
invalidConfig = T.unpack $ T.replace "globalTimeout" "globalTiimeout" $ T.pack exampleConfig -- no-spell-check

spec :: Spec
spec = describe "ExampleConfig" $ do
  it "example config should be valid" $
    doesNotThrow (verifyConfig exampleConfig :: IO ()) `shouldReturn` True
  it "rejects config with unknown fields" $
    doesNotThrow (verifyConfig invalidConfig :: IO ()) `shouldReturn` False
