module Prolog.Programming.CodeAnalysis.Config (
  configuredRules,
  defaultCodeAnalysisConfig,
)
where

import Data.Maybe (catMaybes)
import Prolog.Programming.CodeAnalysis.Rules.ConsistentArity (consistentArityRule)
import Prolog.Programming.CodeAnalysis.Rules.Cuts (cutsRule)
import Prolog.Programming.CodeAnalysis.Rules.SingletonVariables (singletonVariablesRule)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  ConsistentArityConfig (ConsistentArityConfig),
  CutUsageConfig (..),
  Rule,
  SingletonVariablesConfig (..),
  WithSeverity (..),
 )

configuredRules :: CodeAnalysisConfig -> [WithSeverity Rule]
configuredRules
  CodeAnalysisConfig {
    singletonVariables = SingletonVariablesConfig singletonVarsCfg
    , cutUsage = CutUsageConfig cutsCfg
    , consistentArity = ConsistentArityConfig consistentArityCfg
    } =
    catMaybes
      [ toConfigured singletonVarsCfg (const singletonVariablesRule)
      , toConfigured cutsCfg cutsRule
      , toConfigured consistentArityCfg consistentArityRule
      ]
    where
      toConfigured :: CodeAnalysisRuleConfig a -> (a -> Rule) -> Maybe (WithSeverity Rule)
      toConfigured Ignore _ = Nothing
      toConfigured (Detect severity' extra) build = Just (WithSeverity severity' (build extra))

defaultCodeAnalysisConfig :: CodeAnalysisConfig
defaultCodeAnalysisConfig =
  CodeAnalysisConfig {
    singletonVariables = SingletonVariablesConfig Ignore
    , cutUsage = CutUsageConfig Ignore
    , consistentArity = ConsistentArityConfig Ignore
    }
