{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.EarlyRecursion (earlyRecursionChecker) where

import qualified Data.Set as Set (member)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Signature (Signature), Term (..))
import Prolog.Programming.CodeAnalysis.Helper (grabPredicateIdentities)
import Prolog.Programming.CodeAnalysis.Types (AdditionalMessage (AdditionalMessage), ClauseRule, Problem (..))
import Text.PrettyPrint.Leijen.Text (empty, indent, string, vsep)

earlyRecursionChecker :: AdditionalMessage -> ClauseRule
earlyRecursionChecker (AdditionalMessage msg) (name, args, goals) = case recursionInfo of
  Nothing -> []
  Just (hasRecursion, lastIsRecursion) -> [toProblem msg (Clause name args goals) | not lastIsRecursion, hasRecursion]
  where
    definedPredicate = Signature name $ length args
    recursionInfo = foldr update Nothing goals
    containsPredicate = Set.member definedPredicate . grabPredicateIdentities False

    update x Nothing = Just (containsPredicate x, isLastCall definedPredicate x)
    update x (Just (h, l)) = Just (containsPredicate x || h, l)

isLastCall :: Signature -> Term -> Bool
isLastCall p (Struct name args) | p == Signature name (length args) = True
isLastCall p (Struct name [arg])
  | name `elem` ["not", "\\+"] = isLastCall p arg
isLastCall p (Struct name [left, right])
  | name == "," = isLastCall p right
  | name == ";" = isLastCall p left || isLastCall p right
isLastCall _ _ = False

toProblem :: Maybe String -> Clause -> Problem
toProblem msg clause =
  Problem {
    problemDisplay =
      vsep
        [ string "Your clause"
        , indent 2 $ string $ pack $ show clause
        , string "seems to use a recursive call that is not the last goal."
        , maybe empty (string . pack) msg
        ]
    }
