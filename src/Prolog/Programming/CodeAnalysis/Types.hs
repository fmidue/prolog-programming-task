{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Prolog.Programming.CodeAnalysis.Types (
  Problem (..),
  Rule,
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  SingletonVariablesConfig (..),
  AdditionalMessage (..),
  CutUsageConfig (..),
  Severity (..),
  WithSeverity (..),
)
where

import GHC.Generics (Generic)
import Language.Prolog (Clause (..))
import Text.PrettyPrint.Leijen.Text (Doc)

-- | Violation found in code
data Problem = Problem {
  -- | Clause the violation appears in
  problemClause :: Clause
  -- | User-facing explanation of the violation
  , problemDisplay :: Doc
  }
  deriving Show

-- | Definition for a code analysis checker that looks for violations in a given clause
type Rule = Clause -> [Problem]

data CodeAnalysisRuleConfig a
  = Ignore
  | Detect {ruleSeverity :: Severity, extraConfig :: a}
  deriving (Eq, Functor, Show)

newtype SingletonVariablesConfig = SingletonVariablesConfig (CodeAnalysisRuleConfig ())
  deriving Show

newtype AdditionalMessage = AdditionalMessage { additionalMessage :: Maybe String }
  deriving (Generic, Monoid, Semigroup, Show)

newtype CutUsageConfig = CutUsageConfig (CodeAnalysisRuleConfig AdditionalMessage)
  deriving Show

-- | Configuration for code analysis checks
data CodeAnalysisConfig = CodeAnalysisConfig {
  -- | Configuration for singletonVariables rule
  singletonVariables :: SingletonVariablesConfig
  -- | Configuration for cutUsage rule
  , cutUsage :: CutUsageConfig
  }
  deriving (Generic, Show)

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
  deriving (Eq, Show)

-- | Container for values with attached severity
data WithSeverity a = WithSeverity {
  severity :: Severity
  , value :: a
  }
  deriving (Foldable, Functor, Traversable)
