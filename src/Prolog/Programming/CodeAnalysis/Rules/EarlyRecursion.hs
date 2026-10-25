{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.EarlyRecursion (earlyRecursionChecker) where

import qualified Data.Set as Set (member)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Signature (Signature), Term (..))
import Prolog.Programming.CodeAnalysis.Helper (grabPredicateIdentities)
import Prolog.Programming.CodeAnalysis.Types (AdditionalMessage (AdditionalMessage), ClauseRule, Problem (..))
import Text.PrettyPrint.Leijen.Text (empty, indent, string, vsep)

earlyRecursionChecker :: AdditionalMessage -> ClauseRule
earlyRecursionChecker (AdditionalMessage msg) (name, args, goals) =
  [toProblem msg (Clause name args goals) | hasViolation definedPredicate goals]
  where
    definedPredicate = Signature name $ length args

hasViolation :: Signature -> [Term] -> Bool
hasViolation p = go False
  where
    containsPredicate = Set.member p . grabPredicateIdentities False
    isPredicate name args = p == Signature name (length args)

    go _ [] = False
    go seen [Struct m [arg]]
      | m `elem` ["not", "\\+"] = go seen [arg]
    go seen [Struct "," [l, r]] = go (seen || containsPredicate l) [r]
    go seen [Struct ";" [l, r]] = go seen [l] || go seen [r]
    go seen [Struct name args] = seen && not (isPredicate name args)
    go seen (t : ts) = go (seen || containsPredicate t) ts

toProblem :: Maybe String -> Clause -> Problem
toProblem msg clause =
  Problem {
    problemDisplay =
      vsep
        [ string "The last goal in your clause"
        , indent 2 $ string $ pack $ show clause
        , string "doesn't seem to be a recursive call despite one being used."
        , maybe empty (string . pack) msg
        ]
    }
