{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}

module Prolog.Programming.CodeAnalysis.Types (
  Problem (..),
  Context,
  ClauseRule,
  ProgramRule,
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  SingletonVariablesConfig (..),
  AdditionalMessage (..),
  CutUsageConfig (..),
  IgnoredPredicates (..),
  InconsistentAritiesConfig (..),
  RecursionConfig (..),
  UngroupedDefinitionsConfig (..),
  Severity (..),
  WithSeverity (..),
  Predicate,
)
where

import Data.Data (Data, Typeable)
import GHC.Generics (Generic)
import Language.Prolog (Clause (..), Program)
import Text.PrettyPrint.Leijen.Text (Doc)

{- FOURMOLU_DISABLE -} -- Remove when https://github.com/fourmolu/fourmolu/issues/552 is fixed
-- | Violation found in code
newtype Problem = Problem {
  -- | User-facing explanation of the violation
  problemDisplay :: Doc
  }
  deriving Show
{- FOURMOLU_ENABLE -}

type Context = Program

type Predicate = (String, Int)

-- | Definition for a code analysis checker that looks for violations in a given clause
type ClauseRule = Clause -> [Problem]

-- | Definition for a code analysis checker that looks for violations in a given program
type ProgramRule = Program -> [Problem]

data CodeAnalysisRuleConfig a
  = Ignore
  | Detect {ruleSeverity :: Severity, extraConfig :: a}
  deriving (Data, Eq, Functor, Show, Typeable)

newtype SingletonVariablesConfig = SingletonVariablesConfig (CodeAnalysisRuleConfig ())
  deriving (Data, Show)

newtype AdditionalMessage = AdditionalMessage {additionalMessage :: Maybe String}
  deriving (Data, Generic, Show)

newtype CutUsageConfig = CutUsageConfig (CodeAnalysisRuleConfig AdditionalMessage)
  deriving (Data, Show)

newtype IgnoredPredicates = IgnoredPredicates {ignorePredicates :: [String]}
  deriving (Data, Generic, Show)

newtype InconsistentAritiesConfig = InconsistentAritiesConfig (CodeAnalysisRuleConfig IgnoredPredicates)
  deriving (Data, Generic, Show)

newtype UngroupedDefinitionsConfig = UngroupedDefinitionsConfig (CodeAnalysisRuleConfig ())
  deriving (Data, Generic, Show)

newtype RecursionConfig = RecursionConfig (CodeAnalysisRuleConfig AdditionalMessage)
  deriving (Data, Show)

{- FOURMOLU_DISABLE -} -- Remove when https://github.com/fourmolu/fourmolu/issues/552 is fixed
-- | Configuration for code analysis checks
data CodeAnalysisConfig = CodeAnalysisConfig {
  -- | Configuration for singletonVariables rule
  singletonVariables :: SingletonVariablesConfig
  -- | Configuration for cutUsage rule
  , cutUsage :: CutUsageConfig
  -- | Configuration for inconsistentArities rule
  , inconsistentArities :: InconsistentAritiesConfig
  -- | Configuration for ungroupedDefinitions rule
  , ungroupedDefinitions :: UngroupedDefinitionsConfig
  -- | Configuration for recursion rule
  , recursion :: RecursionConfig
  }
  deriving (Data, Generic, Show)

{- | Classification for seriousness of violation

The differentiation between `Hint` and `Warn` is of personal taste.
-}
data Severity
  = {- | Minor violation of standard code conventions

    Example violation: redundant braces
    -}
    Hint
  | {- | Moderate violation of standard code conventions

    Example violation: working at the end of a list even though it is not necessary
    -}
    Warn
  | {- | Severe violation of standard code conventions or task restrictions

    Example violation: cut operator was used even though the use of it was forbidden
    -}
    Error
  deriving (Data, Eq, Show)
{- FOURMOLU_ENABLE -}

-- | Container for values with attached severity
data WithSeverity a = WithSeverity {
  severity :: Severity
  , value :: a
  }
  deriving (Foldable, Functor, Traversable)
