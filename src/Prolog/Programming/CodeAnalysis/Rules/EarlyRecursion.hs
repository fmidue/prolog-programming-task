{-# LANGUAGE OverloadedStrings #-}

module Prolog.Programming.CodeAnalysis.Rules.EarlyRecursion (earlyRecursionChecker) where

import qualified Data.Set as Set (member)
import Data.Text.Lazy (pack)
import Language.Prolog (Clause (..), Signature (Signature), Term (..))
import Prolog.Programming.CodeAnalysis.Helper (grabPredicateIdentities)
import Prolog.Programming.CodeAnalysis.Types (ClauseRule, Problem (..))
import Text.PrettyPrint.Leijen.Text (indent, string, vsep)

earlyRecursionChecker :: ClauseRule
earlyRecursionChecker (name, args, goals) = case recursionInfo of
  Nothing -> []
  Just (hasRecursion, lastIsRecursion) -> [toProblem (Clause name args goals) | not lastIsRecursion, hasRecursion]
  where
    definedPredicate = Signature name $ length args
    recursionInfo = foldr update Nothing goals
    containsPredicate = Set.member definedPredicate . grabPredicateIdentities False

    update x Nothing = Just (containsPredicate x, isLastCall definedPredicate x)
    update x (Just (h, l)) = Just (containsPredicate x || h, l)

isLastCall :: Signature -> Term -> Bool
isLastCall p (Struct name args)
  | p == Signature name (length args) = True
  | name `elem` ["not", "\\+"] = all (isLastCall p) args
  | name == "," && not (null args) = isLastCall p $ last args
  | name == ";" = any (isLastCall p) args
  | otherwise = False
isLastCall _ _ = False

toProblem :: Clause -> Problem
toProblem clause =
  Problem {
    problemDisplay =
      vsep
        [ string "Your clause"
        , indent 2 $ string $ pack $ show clause
        , string "seems to use a recursive call that is not the last goal."
        ]
    }
