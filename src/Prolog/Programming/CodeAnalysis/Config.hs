module Prolog.Programming.CodeAnalysis.Config (
  configuredRules,
  emptyCodeAnalysisConfig,
)
where

import Data.Maybe (catMaybes)
import Prolog.Programming.CodeAnalysis.Rules.Cuts (cutsChecker)
import Prolog.Programming.CodeAnalysis.Rules.InconsistentArity (inconsistentArityChecker)
import Prolog.Programming.CodeAnalysis.Rules.SingletonVariables (singletonVariablesChecker)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  Context,
  CutUsageConfig (..),
  InconsistentArityConfig (InconsistentArityConfig),
  ProgramRule,
  SingletonVariablesConfig (..),
  WithSeverity (..),
 )

configuredRules :: CodeAnalysisConfig -> Context -> [WithSeverity ProgramRule]
configuredRules
  CodeAnalysisConfig {
    singletonVariables = SingletonVariablesConfig singletonVarsCfg
    , cutUsage = CutUsageConfig cutsCfg
    , inconsistentArity = InconsistentArityConfig inconsistentArityCfg
    }
  taskAndHiddenDefinitions =
    catMaybes
      [ toConfigured singletonVarsCfg (concatMap . const singletonVariablesChecker)
      , toConfigured cutsCfg (concatMap . cutsChecker)
      , toConfigured inconsistentArityCfg (inconsistentArityChecker taskAndHiddenDefinitions)
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
    , inconsistentArity = InconsistentArityConfig Ignore
    }
