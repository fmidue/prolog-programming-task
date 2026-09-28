{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Prolog.Programming.Print where

import Control.Monad (void)
import qualified Data.Aeson.KeyMap as KM (singleton, union)
import qualified Data.ByteString.Char8 as BS
import Data.List (intercalate)
import Data.Text (pack)
import Data.Yaml (Object, ToJSON (..), Value (..), object, (.=))
import Data.Yaml.Pretty (defConfig, encodePretty, setConfCompare)
import Prolog.Programming.CodeAnalysis.Types (
  AdditionalMessage (..),
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  CutUsageConfig (..),
  Severity (..),
  SingletonVariablesConfig (..),
 )
import Prolog.Programming.Types (
  Expection (..),
  Include (..),
  Requirement (..),
  Spec (..),
  TaskConfig,
  TaskInstance (..),
  Timeout (..),
  TreeStyle (..),
  Visibility (..),
  Visualize (..),
 )

encode :: ToJSON a => a -> BS.ByteString
encode = encodePretty $ setConfCompare compare defConfig

printInstance :: TaskInstance -> String
printInstance TaskInstance {..} =
  intercalate
    "-------------------------\n"
    $ [ BS.unpack $ encode taskConfig
      , visiblePredicates
      , sampleSolution
      ]
      ++ [hiddenPredicates | not (null hiddenPredicates)]

instance ToJSON TreeStyle where
  toJSON QueryStyle = String "query"
  toJSON ResolutionStyle = String "resolution"

statusToJSON :: CodeAnalysisRuleConfig () -> Object
statusToJSON Ignore = KM.singleton "status" $ String "ignore"
statusToJSON (Detect severity ()) = case severity of
  Hint -> KM.singleton "status" $ String "hint"
  Warn -> KM.singleton "status" $ String "warn"
  Error -> KM.singleton "status" $ String "reject"

ruleToJSON :: ToJSON a => CodeAnalysisRuleConfig a -> Value
ruleToJSON Ignore = object ["status" .= statusToJSON Ignore]
ruleToJSON cfg@(Detect _ extra) = case toJSON extra of
  Object obj -> Object $ KM.union (statusToJSON (void cfg)) obj
  Array _ -> Object $ statusToJSON (void cfg)
  Null -> Object $ statusToJSON (void cfg)
  _ -> error "Extra config must be encoded as object, array or null"

instance ToJSON AdditionalMessage where
  toJSON (AdditionalMessage cMsg) = case cMsg of
    Nothing -> Null
    Just msg -> object ["additionalMessage" .= msg]

instance ToJSON SingletonVariablesConfig where
  toJSON (SingletonVariablesConfig cfg) = ruleToJSON cfg

instance ToJSON CutUsageConfig where
  toJSON (CutUsageConfig cfg) = ruleToJSON cfg

instance ToJSON CodeAnalysisConfig where
  toJSON CodeAnalysisConfig {..} =
    object
      [ "singletonVariables" .= singletonVariables
      , "cutUsage" .= cutUsage
      ]

instance ToJSON Spec where
  toJSON (Spec visibility visualize ex to req) = String $ pack $ to' ++ ex' ++ visualize' ++ visibility' ++ req'
    where
      visibility' = case visibility of
        Hidden "" -> "!"
        Hidden msg -> "!(" ++ show msg ++ ")"
        _ -> ""
      visualize' = case visualize of
        ShowTree -> "@"
        _ -> ""
      ex' = case ex of
        NegativeResult -> "-"
        _ -> ""
      to' = case to of
        LocalTimeout duration -> "[" ++ show duration ++ "]"
        _ -> ""
      req' = case req of
        StatementToCheck terms -> intercalate ", " $ map show terms
        QueryWithAnswers ts tss -> intercalate ", " (map show ts) ++ ": " ++ intercalate ", " (map (show . head) tss)
        NewPredDecl term description -> "new " ++ show term ++ ": " ++ description

instance ToJSON (Include a) where
  toJSON Yes = String "yes"
  toJSON Filtered = String "filtered"
  toJSON No {} = String "no"

deriving instance ToJSON TaskConfig
