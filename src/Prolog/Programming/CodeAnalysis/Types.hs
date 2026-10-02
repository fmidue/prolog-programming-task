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
  Predicate (..),
  ForbiddenPredicates (..),
  PredicatesConfig (..),
)
where

import Data.Data (Typeable)
import Data.Set (Set)
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

data Predicate = Predicate {
  predicateName :: String
  , predicateArity :: Int
  }
  deriving (Eq, Generic, Ord)

instance Show Predicate where
  show (Predicate name arity) = name ++ "/" ++ show arity

-- | Definition for a code analysis checker that looks for violations in a given clause
type ClauseRule = Clause -> [Problem]

-- | Definition for a code analysis checker that looks for violations in a given program
type ProgramRule = Program -> [Problem]

data CodeAnalysisRuleConfig a
  = Ignore
  | Detect Severity a
  deriving (Eq, Functor, Show, Typeable)

newtype SingletonVariablesConfig = SingletonVariablesConfig (CodeAnalysisRuleConfig ())
  deriving Show

newtype AdditionalMessage = AdditionalMessage {additionalMessage :: Maybe String}
  deriving (Generic, Show)

newtype CutUsageConfig = CutUsageConfig (CodeAnalysisRuleConfig AdditionalMessage)
  deriving Show

newtype IgnoredPredicates = IgnoredPredicates {ignorePredicates :: [String]}
  deriving (Generic, Show)

newtype InconsistentAritiesConfig = InconsistentAritiesConfig (CodeAnalysisRuleConfig IgnoredPredicates)
  deriving (Generic, Show)

newtype UngroupedDefinitionsConfig = UngroupedDefinitionsConfig (CodeAnalysisRuleConfig ())
  deriving (Generic, Show)

newtype RecursionConfig = RecursionConfig (CodeAnalysisRuleConfig AdditionalMessage)
  deriving Show

newtype ForbiddenPredicates = ForbiddenPredicates {forbiddenPredicates :: Set Predicate}
  deriving (Generic, Show)

newtype PredicatesConfig = PredicatesConfig (CodeAnalysisRuleConfig ForbiddenPredicates)
  deriving (Generic, Show)

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
  -- | Configuration for predicates rule
  , predicates :: PredicatesConfig
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
{- FOURMOLU_ENABLE -}

-- | Container for values with attached severity
data WithSeverity a = WithSeverity {
  severity :: Severity
  , value :: a
  }
  deriving (Foldable, Functor, Traversable)
