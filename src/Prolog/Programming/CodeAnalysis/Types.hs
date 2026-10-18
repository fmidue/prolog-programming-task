{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Prolog.Programming.CodeAnalysis.Types (
  Problem (..),
  Context,
  ClauseRule,
  ProgramRule,
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig,
  SingletonVariablesConfig (..),
  AdditionalMessage (..),
  CutUsageConfig (..),
  IgnoredPredicates (..),
  InconsistentAritiesConfig (..),
  RecursionConfig (..),
  UngroupedDefinitionsConfig (..),
  Severity (..),
  WithSeverity (..),
  ForbiddenPredicatesConfig (..),
)
where

import Autolib.Reader (Reader)
import Autolib.Set ()
import Autolib.ToDoc (ToDoc)
import Data.Data (Data)
import Data.Set (Set)
import GHC.Generics (Generic)
import Language.Prolog (Atom, Goal, Signature (..), Term)
import Text.PrettyPrint.Leijen.Text (Doc)

{- FOURMOLU_DISABLE -} -- Remove when https://github.com/fourmolu/fourmolu/issues/552 is fixed
-- | Violation found in code
newtype Problem = Problem {
  -- | User-facing explanation of the violation
  problemDisplay :: Doc
  }
  deriving Show
{- FOURMOLU_ENABLE -}

type Context = [(Atom, [Term], [Goal])]

-- | Definition for a code analysis checker that looks for violations in a given clause
type ClauseRule = (Atom, [Term], [Goal]) -> [Problem]

-- | Definition for a code analysis checker that looks for violations in a given program
type ProgramRule = [(Atom, [Term], [Goal])] -> [Problem]

type CodeAnalysisRuleConfig a = Maybe (WithSeverity a)

newtype SingletonVariablesConfig = SingletonVariablesConfig (CodeAnalysisRuleConfig ())
  deriving (Data, Generic, Reader, Show, ToDoc)

newtype AdditionalMessage = AdditionalMessage {additionalMessage :: Maybe String}
  deriving (Data, Generic, Reader, Show, ToDoc)

newtype CutUsageConfig = CutUsageConfig (CodeAnalysisRuleConfig AdditionalMessage)
  deriving (Data, Generic, Reader, Show, ToDoc)

newtype IgnoredPredicates = IgnoredPredicates {ignorePredicates :: [String]}
  deriving (Data, Generic, Reader, Show, ToDoc)

newtype InconsistentAritiesConfig = InconsistentAritiesConfig (CodeAnalysisRuleConfig IgnoredPredicates)
  deriving (Data, Generic, Reader, Show, ToDoc)

newtype UngroupedDefinitionsConfig = UngroupedDefinitionsConfig (CodeAnalysisRuleConfig ())
  deriving (Data, Generic, Reader, Show, ToDoc)

newtype RecursionConfig = RecursionConfig (CodeAnalysisRuleConfig AdditionalMessage)
  deriving (Data, Generic, Reader, Show, ToDoc)

newtype ForbiddenPredicatesConfig = ForbiddenPredicatesConfig {forbiddenPredicateSet :: Set Signature}
  deriving (Data, Generic, Reader, Show, ToDoc)

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
  -- | Configuration for forbiddenPredicates rule
  , forbiddenPredicates :: ForbiddenPredicatesConfig
  }
  deriving (Data, Generic, Show, Reader, ToDoc)

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
  deriving (Data, Eq, Generic, Show, Reader, ToDoc)
{- FOURMOLU_ENABLE -}

-- | Container for values with attached severity
data WithSeverity a = WithSeverity {
  severity :: Severity
  , value :: a
  }
  deriving (Data, Eq, Foldable, Functor, Generic, Reader, Show, ToDoc, Traversable)

deriving instance Data Signature
deriving instance Generic Signature
deriving instance Reader Signature
deriving instance ToDoc Signature
