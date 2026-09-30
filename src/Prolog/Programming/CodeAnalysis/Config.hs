module Prolog.Programming.CodeAnalysis.Config (
  configuredRules,
  emptyCodeAnalysisConfig,
)
where

import Data.Maybe (catMaybes)
import Prolog.Programming.CodeAnalysis.Rules.ConsistentArity (consistentArityChecker)
import Prolog.Programming.CodeAnalysis.Rules.Cuts (cutsChecker)
import Prolog.Programming.CodeAnalysis.Rules.SingletonVariables (singletonVariablesChecker)
import Prolog.Programming.CodeAnalysis.Rules.UngroupedDefinitions (ungroupedDefinitionsChecker)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  ConsistentArityConfig (ConsistentArityConfig),
  Context,
  CutUsageConfig (..),
  ProgramRule,
  SingletonVariablesConfig (..),
  UngroupedDefinitionsConfig (UngroupedDefinitionsConfig),
  WithSeverity (..),
 )

configuredRules :: CodeAnalysisConfig -> Context -> [WithSeverity ProgramRule]
configuredRules
  CodeAnalysisConfig {
    singletonVariables = SingletonVariablesConfig singletonVarsCfg
    , cutUsage = CutUsageConfig cutsCfg
    , consistentArity = ConsistentArityConfig consistentArityCfg
    , ungroupedDefinitions = UngroupedDefinitionsConfig ungroupedDefinitionsCfg
    }
  taskAndHiddenDefinitions =
    catMaybes
      [ toConfigured singletonVarsCfg (concatMap . const singletonVariablesChecker)
      , toConfigured cutsCfg (concatMap . cutsChecker)
      , toConfigured consistentArityCfg (consistentArityChecker taskAndHiddenDefinitions)
      , toConfigured ungroupedDefinitionsCfg (const ungroupedDefinitionsChecker)
      ]
    where
      toConfigured :: CodeAnalysisRuleConfig a -> (a -> ProgramRule) -> Maybe (WithSeverity ProgramRule)
      toConfigured Ignore _ = Nothing
      toConfigured (Detect severity' extra) build = Just (WithSeverity severity' (build extra))

emptyCodeAnalysisConfig :: CodeAnalysisConfig
emptyCodeAnalysisConfig =
  CodeAnalysisConfig {
    singletonVariables = SingletonVariablesConfig Ignore
    , cutUsage = CutUsageConfig Ignore
    , consistentArity = ConsistentArityConfig Ignore
    , ungroupedDefinitions = UngroupedDefinitionsConfig Ignore
    }
