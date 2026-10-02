module Prolog.Programming.CodeAnalysis.Config (
  configuredRules,
  emptyCodeAnalysisConfig,
)
where

import Data.Maybe (catMaybes)
import Prolog.Programming.CodeAnalysis.Rules.ClauseAmount (clauseAmountChecker)
import Prolog.Programming.CodeAnalysis.Rules.Cuts (cutsChecker)
import Prolog.Programming.CodeAnalysis.Rules.InconsistentArities (inconsistentAritiesChecker)
import Prolog.Programming.CodeAnalysis.Rules.Recursion (recursionChecker)
import Prolog.Programming.CodeAnalysis.Rules.SingletonVariables (singletonVariablesChecker)
import Prolog.Programming.CodeAnalysis.Rules.UngroupedDefinitions (ungroupedDefinitionsChecker)
import Prolog.Programming.CodeAnalysis.Types (
  ClauseAmountConfig (ClauseAmountConfig),
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  Context,
  CutUsageConfig (..),
  InconsistentAritiesConfig (InconsistentAritiesConfig),
  ProgramRule,
  RecursionConfig (..),
  SingletonVariablesConfig (..),
  UngroupedDefinitionsConfig (UngroupedDefinitionsConfig),
  WithSeverity (..),
 )

configuredRules :: CodeAnalysisConfig -> Context -> [WithSeverity ProgramRule]
configuredRules
  CodeAnalysisConfig {
    singletonVariables = SingletonVariablesConfig singletonVarsCfg
    , cutUsage = CutUsageConfig cutsCfg
    , inconsistentArities = InconsistentAritiesConfig inconsistentAritiesCfg
    , ungroupedDefinitions = UngroupedDefinitionsConfig ungroupedDefinitionsCfg
    , recursion = RecursionConfig recursionCfg
    , clauseAmount = ClauseAmountConfig clauseAmountCfg
    }
  taskAndHiddenDefinitions =
    catMaybes
      [ toConfigured singletonVarsCfg (concatMap . const singletonVariablesChecker)
      , toConfigured cutsCfg (concatMap . cutsChecker)
      , toConfigured inconsistentAritiesCfg (inconsistentAritiesChecker taskAndHiddenDefinitions)
      , toConfigured ungroupedDefinitionsCfg (const ungroupedDefinitionsChecker)
      , toConfigured recursionCfg recursionChecker
      , toConfigured clauseAmountCfg clauseAmountChecker
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
    , inconsistentArities = InconsistentAritiesConfig Ignore
    , ungroupedDefinitions = UngroupedDefinitionsConfig Ignore
    , recursion = RecursionConfig Ignore
    , clauseAmount = ClauseAmountConfig Ignore
    }
