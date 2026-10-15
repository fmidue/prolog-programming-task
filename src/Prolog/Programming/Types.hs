{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Prolog.Programming.Types where

import Autolib.Reader (Reader (..), my_braces, my_comma, my_equals, my_reserved)
import Autolib.ToDoc (ToDoc (..), docParen, fcp, named_dutch_record, text, (<+>))
import Control.Monad (void)
import Data.Data (Data)
import Data.Void (Void)
import GHC.Generics (Generic)
import Language.Prolog (Clause (..), Term (..), VariableName (..))
import Prolog.Programming.CodeAnalysis.Types (CodeAnalysisConfig)
import Prolog.Programming.Data (Code)

type TimeoutDuration = Int

data TreeStyle = QueryStyle | ResolutionStyle
  deriving (Data, Generic, Reader, Show, ToDoc)

type IncludeTask = Include ()

type IncludeHidden = Include Void

data Include a = Yes | Filtered | No a
  deriving (Data, Eq, Generic, Reader, Show, ToDoc)

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
  , rigorousValidation :: Bool
  }
  deriving (Data, Generic, Reader, Show, ToDoc)

data TaskInstance = TaskInstance {
  taskConfig :: TaskConfig
  , sampleSolution :: Code
  , visiblePredicates :: Code
  , hiddenPredicates :: Code
  }
  deriving (Generic, Reader, Show, ToDoc)

data Spec = Spec {
  specVisibility :: Visibility
  , specVisualize :: Visualize
  , specExpection :: Expection
  , specTimeout :: Timeout
  , specRequirement :: Requirement
  }
  deriving (Data, Generic, Reader, Show, ToDoc)

data Visibility = Hidden String | Visible
  deriving (Data, Generic, Reader, Show, ToDoc)

data Visualize = ShowTree | DontShowTree
  deriving (Data, Generic, Reader, Show, ToDoc)

data Expection = PositiveResult | NegativeResult
  deriving (Data, Generic, Reader, Show, ToDoc)

data Timeout = GlobalTimeout | LocalTimeout Int
  deriving (Data, Generic, Reader, Show, ToDoc)

data Requirement
  = StatementToCheck [Term]
  | QueryWithAnswers [Term] [[Term]]
  | NewPredDecl Term String
  deriving (Data, Generic, Reader, Show, ToDoc)

deriving instance Reader VariableName
deriving instance ToDoc VariableName

deriving instance Reader Term
deriving instance ToDoc Term

instance ToDoc Clause where
  toDocPrec p x =
    docParen (p >= fcp) $ case x of
      Clause lhs' rhs' ->
        named_dutch_record
          (text "Clause")
          [ text "lhs" <+> text "=" <+> toDocPrec p lhs'
          , text "rhs_" <+> text "=" <+> toDocPrec p rhs'
          ]
      ClauseFn _ _ -> error "Cannot encode ClauseFn into document"

instance Reader Clause where
  atomic_readerPrec _ = do
    my_reserved "Clause"
    my_braces $ do
      lhs' <- my_reserved "lhs" *> my_equals *> reader
      void my_comma
      rhs' <- my_reserved "rhs_" *> my_equals *> reader
      return $ Clause lhs' rhs'
