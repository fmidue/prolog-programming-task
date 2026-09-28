module Prolog.Programming.CodeAnalysis.Config (
  configuredRules,
  defaultCodeAnalysisConfig,
)
where

import Data.Maybe (catMaybes)
import Prolog.Programming.CodeAnalysis.Rules.ConsistentArity (consistentArityChecker)
import Prolog.Programming.CodeAnalysis.Rules.Cuts (cutsChecker)
import Prolog.Programming.CodeAnalysis.Rules.SingletonVariables (singletonVariablesChecker)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  ConsistentArityConfig (ConsistentArityConfig),
  Context,
  CutUsageConfig (..),
  Rule,
  SingletonVariablesConfig (..),
  WithSeverity (..),
 )

configuredRules :: CodeAnalysisConfig -> Context -> [WithSeverity Rule]
configuredRules
  CodeAnalysisConfig {
    singletonVariables = SingletonVariablesConfig singletonVarsCfg
    , cutUsage = CutUsageConfig cutsCfg
    , consistentArity = ConsistentArityConfig consistentArityCfg
    }
  context =
    catMaybes
      [ toConfigured singletonVarsCfg (const singletonVariablesChecker)
      , toConfigured cutsCfg cutsChecker
      , toConfigured consistentArityCfg (consistentArityChecker context)
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
