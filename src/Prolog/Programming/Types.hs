{-# LANGUAGE DeriveGeneric #-}

module Prolog.Programming.Types where

import Data.Void (Void)
import GHC.Generics (Generic)
import Language.Prolog (Term)
import Prolog.Programming.CodeAnalysis.Types (CodeAnalysisConfig)

type TimeoutDuration = Int

data TreeStyle = QueryStyle | ResolutionStyle

type IncludeTask = Include ()

type IncludeHidden = Include Void

data Include a = Yes | Filtered | No a

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
  deriving Generic

data Spec = Spec {
  specVisibility :: Visibility
  , specVisualize :: Visualize
  , specExpection :: Expection
  , specTimeout :: Timeout
  , specRequirement :: Requirement
  }
  deriving Show

data Visibility = Hidden String | Visible
  deriving Show

data Visualize = ShowTree | DontShowTree
  deriving Show

data Expection = PositiveResult | NegativeResult
  deriving Show

data Timeout = GlobalTimeout | LocalTimeout Int
  deriving Show

data Requirement
  = StatementToCheck [Term]
  | QueryWithAnswers [Term] [[Term]]
  | NewPredDecl Term String
  deriving Show
