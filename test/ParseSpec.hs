{-# LANGUAGE QuasiQuotes #-}

module ParseSpec where

import Data.Either (isLeft, isRight)
import Prolog.Programming.Parser (parseInstance)
import Test.Hspec (Spec, describe, it, shouldSatisfy)
import qualified Text.RawString.QQ as RS (r)

spec :: Spec
spec = describe "Parser" $ do
  describe "parseInstance" $ do
    it "rejects instance without anything" $ do
      parseInstance "" `shouldSatisfy` isLeft

    it "rejects instance without three sections" $ do
      let raw =
            [RS.r|
----------
              |]
       in parseInstance raw `shouldSatisfy` isLeft

    it "accepts instance with three sections" $ do
      let raw =
            [RS.r|
globalTimeout: 1000
----------
----------
              |]
       in parseInstance raw `shouldSatisfy` isRight

    it "rejects instances with unknown fields" $ do
      let raw =
            [RS.r|
globalTiimeout: 1000 # no-spell-check
----------
----------
              |]
       in parseInstance raw `shouldSatisfy` isLeft
