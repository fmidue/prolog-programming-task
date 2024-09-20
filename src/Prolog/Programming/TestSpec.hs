module Prolog.Programming.TestSpec where

import Data.Maybe (listToMaybe)
import Data.Void ( Void )

import Language.Prolog (Term (..))

type TimeoutDuration = Int

data TreeStyle = QueryStyle | ResolutionStyle

type IncludeTask = Include ()
type IncludeHidden = Include Void
data Include a = Yes | Filtered | No a

data SpecLine
  = TimeoutSpec TimeoutDuration
  | TreeStyleSpec TreeStyle
  | IncludeTaskSpec IncludeTask
  | IncludeHiddenSpec IncludeHidden
  | TestSpec Spec

partitionSpecLine :: [SpecLine] -> (Maybe TimeoutDuration, Maybe TreeStyle, Maybe IncludeTask, Maybe IncludeHidden, [Spec])
partitionSpecLine = (\(ts,ss,ihs,its,xs) -> (listToMaybe ts, listToMaybe ss, listToMaybe ihs, listToMaybe its,xs)) . mconcat . map sortLine
  where
    sortLine (TimeoutSpec t)       = ([t],[],[],[],[])
    sortLine (TreeStyleSpec s)     = ([],[s],[],[],[])
    sortLine (IncludeTaskSpec i)   = ([],[],[i],[],[])
    sortLine (IncludeHiddenSpec i) = ([],[],[],[i],[])
    sortLine (TestSpec x)          = ([],[],[],[],[x])

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
