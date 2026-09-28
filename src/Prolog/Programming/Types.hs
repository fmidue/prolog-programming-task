{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Prolog.Programming.Types where

import Data.Data (Data)
import Data.Void (Void)
import GHC.Generics (Generic)
import Language.Prolog (Term)
import Prolog.Programming.CodeAnalysis.Types (CodeAnalysisConfig)

type TimeoutDuration = Int

data TreeStyle = QueryStyle | ResolutionStyle
  deriving (Data, Show)

type IncludeTask = Include ()

type IncludeHidden = Include Void

data Include a = Yes | Filtered | No a
  deriving (Data, Eq, Show)

type AllowListMatching = Bool

type ShowSWISHButton = Bool

data TaskConfig = TaskConfig {
  globalTimeout :: TimeoutDuration
  , treeStyle :: TreeStyle
  , includeTaskDefinitions :: IncludeTask
  , includeHiddenDefinitions :: IncludeHidden
  , allowListPatternMatching :: AllowListMatching
  , showSWISHButton :: ShowSWISHButton
  , codeAnalysis :: CodeAnalysisConfig
  , specifications :: [Spec]
  }
  deriving (Data, Generic, Show)

data TaskInstance = TaskInstance {
  taskConfig :: TaskConfig
  , sampleSolution :: String
  , visiblePredicates :: String
  , hiddenPredicates :: String
  }
  deriving (Generic, Show)

data Spec = Spec {
  specVisibility :: Visibility
  , specVisualize :: Visualize
  , specExpection :: Expection
  , specTimeout :: Timeout
  , specRequirement :: Requirement
  }
  deriving (Data, Show)

data Visibility = Hidden String | Visible
  deriving (Data, Show)

data Visualize = ShowTree | DontShowTree
  deriving (Data, Show)

data Expection = PositiveResult | NegativeResult
  deriving (Data, Show)

data Timeout = GlobalTimeout | LocalTimeout Int
  deriving (Data, Show)

data Requirement
  = StatementToCheck [Term]
  | QueryWithAnswers [Term] [[Term]]
  | NewPredDecl Term String
  deriving (Data, Show)
