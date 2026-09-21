module Prolog.Programming.TestSpec where

import Data.Void ( Void )

import Language.Prolog (Term (..))
import Control.Applicative ((<|>))

type TimeoutDuration = Int

data TreeStyle = QueryStyle | ResolutionStyle

type IncludeTask = Include ()
type IncludeHidden = Include Void
data Include a = Yes | Filtered | No a

type AllowListMatching = Bool
type ShowSWISHButton = Bool

data SpecLine
  = TimeoutSpec TimeoutDuration
  | TreeStyleSpec TreeStyle
  | IncludeTaskSpec IncludeTask
  | IncludeHiddenSpec IncludeHidden
  | ListMatchSpec AllowListMatching
  | ShowsSWISHButtonSpec ShowSWISHButton
  | TestSpec Spec

data TaskConfig m = TaskConfig
  { mTimeout :: m TimeoutDuration
  , mStyle :: m TreeStyle
  , mIncTask :: m IncludeTask
  , mIncHidden :: m IncludeHidden
  , mListMatch :: m AllowListMatching
  , mSWISHButton :: m ShowSWISHButton
  , specifications :: [Spec]
  }

partitionSpecLine :: [SpecLine] -> TaskConfig Maybe
partitionSpecLine = foldl (flip combine) (TaskConfig Nothing Nothing Nothing Nothing Nothing Nothing [])
  where
    combine (TimeoutSpec s) spec = spec { mTimeout = mTimeout spec <|> Just s }
    combine (TreeStyleSpec s) spec = spec { mStyle = mStyle spec <|> Just s }
    combine (IncludeTaskSpec s) spec = spec { mIncTask = mIncTask spec <|> Just s }
    combine (IncludeHiddenSpec s) spec = spec { mIncHidden = mIncHidden spec <|> Just s }
    combine (ListMatchSpec s) spec = spec { mListMatch = mListMatch spec <|> Just s }
    combine (ShowsSWISHButtonSpec s) spec = spec { mSWISHButton = mSWISHButton spec <|> Just s }
    combine (TestSpec s) spec = spec { specifications = specifications spec ++ [s] }


data Spec = Spec Visibility Visualize Expection Timeout Requirement
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

defaultOptions :: Requirement -> Spec
defaultOptions = Spec Visible DontShowTree PositiveResult GlobalTimeout

queryWithAnswers :: [Term] -> [[Term]] -> Spec
queryWithAnswers q as =  defaultOptions $ QueryWithAnswers q as

statementToCheck :: [Term] -> Spec
statementToCheck ts = defaultOptions $ StatementToCheck ts

newPredDecl :: Term -> String -> Spec
newPredDecl t s = defaultOptions $ NewPredDecl t s

hidden :: String -> Spec -> Spec
hidden s (Spec _ t e to r) = Spec (Hidden s) t e to r

withTree :: Spec -> Spec
withTree (Spec v _ e to r) = Spec v ShowTree e to r

withTreeNegative :: Spec -> Spec
withTreeNegative = negative . withTree

negative :: Spec -> Spec
negative (Spec v t _ to r) = Spec v t NegativeResult to r

localTimeout :: Int -> Spec -> Spec
localTimeout d (Spec v t e _ r) = Spec v t e (LocalTimeout d) r
