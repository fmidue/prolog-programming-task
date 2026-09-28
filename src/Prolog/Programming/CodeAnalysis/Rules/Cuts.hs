{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.Cuts (cutsChecker) where

import Data.Data (Data)
import Data.Generics (everything, mkQ)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Term (..))
import Prolog.Programming.CodeAnalysis.Types (AdditionalMessage (..), Problem (..), Rule (..))
import Text.PrettyPrint.Leijen.Text (empty, indent, linebreak, string, vsep)

cutsChecker :: AdditionalMessage -> Rule
cutsChecker (AdditionalMessage cMsg) = ClauseRule $ \clause ->
  [toProblem cMsg clause | cutExistsInClause clause]

cutExistsInClause :: Clause -> Bool
cutExistsInClause (Clause _ rhs) = any containsCut rhs
cutExistsInClause _ = False

containsCut :: Data a => a -> Bool
containsCut = everything (||) $ mkQ False $ \case
  Cut _ -> True
  _ -> False

toProblem :: Maybe String -> Clause -> Problem
toProblem cMsg clause =
  Problem {
    problemDisplay =
      vsep
        [ string "Your clause"
        , indent 2 $ string $ pack $ show clause
        , string "makes use of the cut (!) operator." <> linebreak
        , maybe empty (string . pack) cMsg
        ]
    }
