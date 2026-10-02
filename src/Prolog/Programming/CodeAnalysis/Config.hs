module Prolog.Programming.CodeAnalysis.Config (
  configuredRules,
  emptyCodeAnalysisConfig,
)
where

import Data.Maybe (catMaybes)
import qualified Data.Set as Set (empty)
import Prolog.Programming.CodeAnalysis.Rules.Cuts (cutsChecker)
import Prolog.Programming.CodeAnalysis.Rules.ForbiddenPredicates (forbiddenPredicatesChecker)
import Prolog.Programming.CodeAnalysis.Rules.InconsistentArities (inconsistentAritiesChecker)
import Prolog.Programming.CodeAnalysis.Rules.Recursion (recursionChecker)
import Prolog.Programming.CodeAnalysis.Rules.SingletonVariables (singletonVariablesChecker)
import Prolog.Programming.CodeAnalysis.Rules.UngroupedDefinitions (ungroupedDefinitionsChecker)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  Context,
  CutUsageConfig (..),
  ForbiddenPredicatesConfig (ForbiddenPredicatesConfig),
  InconsistentAritiesConfig (InconsistentAritiesConfig),
  ProgramRule,
  RecursionConfig (..),
  Severity (Error),
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
    , forbiddenPredicates = ForbiddenPredicatesConfig forbiddenPredicatesCfg
    }
  taskAndHiddenDefinitions =
    catMaybes
      [ toConfigured singletonVarsCfg (concatMap . const singletonVariablesChecker)
      , toConfigured cutsCfg (concatMap . cutsChecker)
      , toConfigured inconsistentAritiesCfg (inconsistentAritiesChecker taskAndHiddenDefinitions)
      , toConfigured ungroupedDefinitionsCfg (const ungroupedDefinitionsChecker)
      , toConfigured recursionCfg recursionChecker
      , Just $ WithSeverity Error $ concatMap (forbiddenPredicatesChecker forbiddenPredicatesCfg)
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
    , forbiddenPredicates = ForbiddenPredicatesConfig Set.empty
    }
