{-# LANGUAGE ScopedTypeVariables #-}

module ExamplesSpec where

import Control.Exception (SomeException, evaluate, try)
import Prolog.Programming.Task (exampleInstance)
import Test.Hspec (Spec, describe, it, shouldReturn)

doesNotThrow :: forall a. a -> IO Bool
doesNotThrow x = do
  result <- try (evaluate x) :: IO (Either SomeException a)
  pure $ case result of
    Left _ -> False
    Right _ -> True

spec :: Spec
spec = describe "Examples" $ do
  it "example instance should be valid" $ do
    doesNotThrow exampleInstance `shouldReturn` True
