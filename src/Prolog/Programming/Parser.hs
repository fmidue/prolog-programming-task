{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Prolog.Programming.Parser (
  parseConfig,
  parseSpec,
) where

import Control.Arrow ((&&&), (>>>))
import Control.Monad (unless, void)

import Data.List (intercalate, isPrefixOf)

import Language.Prolog (Term, term, terms)

import Data.Aeson (Result (..), fromJSON)
import Data.Aeson.Key (toString)
import qualified Data.Aeson.KeyMap as KM (keys)
import Data.Bifunctor (Bifunctor (..))
import qualified Data.ByteString.Char8 as BS (pack)
import Data.Data (Typeable)
import qualified Data.Text as T (unpack)
import Data.Yaml (FromJSON (..), Object, Value (..), decodeEither', withObject, (.!=), (.:?))
import Data.Yaml.Aeson (Parser)
import GHC.Generics (Generic, Rep)
import Prolog.Programming.CodeAnalysis.Config (
  emptyCodeAnalysisConfig,
 )
import Prolog.Programming.CodeAnalysis.Types (
  AdditionalMessage (..),
  CodeAnalysisConfig (..),
  CodeAnalysisRuleConfig (..),
  CutUsageConfig (..),
  IgnoredPredicates (..),
  InconsistentAritiesConfig (..),
  SingletonVariablesConfig (..),
 )
import qualified Prolog.Programming.CodeAnalysis.Types as CA (Severity (..))
import Prolog.Programming.TypeHelper (FieldNames, recordFieldNames, typeName)
import Prolog.Programming.Types (
  Expection (..),
  Include (..),
  IncludeHidden,
  IncludeTask,
  Requirement (..),
  Spec (..),
  TaskConfig (..),
  Timeout (..),
  TreeStyle (..),
  Visibility (..),
  Visualize (..),
 )
import Text.Parsec hiding (Error)

rejectUnknownFields :: [String] -> Object -> Parser ()
rejectUnknownFields known obj =
  unless (null unknown)
    $ fail
    $ "Unknown or forbidden fields: " ++ intercalate ", " unknown
  where
    unknown = filter (`notElem` known) $ map toString $ KM.keys obj

instance FromJSON TreeStyle where
  parseJSON (String "query") = pure QueryStyle
  parseJSON (String "resolution") = pure ResolutionStyle
  parseJSON _ = fail "Invalid value"

instance FromJSON IncludeTask where
  parseJSON (Bool True) = pure Yes
  parseJSON (String "filtered") = pure Filtered
  parseJSON (Bool False) = pure $ No ()
  parseJSON _ = fail "Invalid value"

instance FromJSON IncludeHidden where
  parseJSON (Bool True) = pure Yes
  parseJSON (String "filtered") = pure Filtered
  parseJSON _ = fail "Invalid value"

instance FromJSON Spec where
  parseJSON (String v) = case parse (parseSpec <* eof) "(spec)" (T.unpack v) of
    Left err -> fail $ show err
    Right s -> pure s
  parseJSON _ = fail "Invalid value type"

parseStatus :: Value -> Parser (CodeAnalysisRuleConfig ())
parseStatus (String "ignore") = pure Ignore
parseStatus (String "hint") = pure $ Detect CA.Hint ()
parseStatus (String "warn") = pure $ Detect CA.Warn ()
parseStatus (String "reject") = pure $ Detect CA.Error ()
parseStatus _ = fail "status must be one of: 'ignore', 'hint', 'warn', or 'reject'"

withRuleParser
  :: forall a b
   . (FieldNames (Rep a), FromJSON a, Generic a, Typeable b)
  => (CodeAnalysisRuleConfig a -> b)
  -> Value
  -> Parser b
withRuleParser cons = withObject (typeName @b) $ \v -> do
  mStatus <- v .:? "status"
  status <- maybe (pure Ignore) parseStatus mStatus

  case status of
    Ignore -> do
      rejectUnknownFields ["status"] v
      pure $ cons Ignore
    base -> case fromJSON (Object v) of
      Error err -> fail $ show err
      Success extra -> do
        rejectUnknownFields ("status" : recordFieldNames @a) v
        pure $ cons (extra <$ base)

instance FromJSON SingletonVariablesConfig where
  parseJSON = withRuleParser SingletonVariablesConfig

instance FromJSON AdditionalMessage where
  parseJSON = withObject "AdditionalMessage" $ \v ->
    AdditionalMessage
      <$> v .:? "additionalMessage"

instance FromJSON CutUsageConfig where
  parseJSON = withRuleParser CutUsageConfig

instance FromJSON IgnoredPredicates where
  parseJSON = withObject "IgnoredPredicates" $ \v ->
    IgnoredPredicates
      <$> v .:? "ignorePredicates" .!= []

instance FromJSON InconsistentAritiesConfig where
  parseJSON = withRuleParser InconsistentAritiesConfig

instance FromJSON CodeAnalysisConfig where
  parseJSON = withObject "CodeAnalysisConfig" $ \v -> do
    rejectUnknownFields (recordFieldNames @CodeAnalysisConfig) v

    CodeAnalysisConfig
      <$> v .:? "singletonVariables" .!= SingletonVariablesConfig Ignore
      <*> v .:? "cutUsage" .!= CutUsageConfig Ignore
      <*> v .:? "inconsistentArities" .!= InconsistentAritiesConfig Ignore

instance FromJSON TaskConfig where
  parseJSON = withObject "TaskConfig" $ \v -> do
    rejectUnknownFields (recordFieldNames @TaskConfig) v

    TaskConfig
      <$> v .:? "globalTimeout" .!= 10000
      <*> v .:? "treeStyle" .!= QueryStyle
      <*> v .:? "includeTaskDefinitions" .!= Yes
      <*> v .:? "includeHiddenDefinitions" .!= Yes
      <*> v .:? "allowListPatternMatching" .!= True
      <*> v .:? "showSWISHButton" .!= False
      <*> v .:? "codeAnalysis" .!= emptyCodeAnalysisConfig
      <*> v .:? "specifications" .!= []

parseConfig :: String -> Either ParseError (TaskConfig, (String, String))
parseConfig = parse (configuration <* eof) "(config)"

configuration
  :: Parsec
       String
       ()
       ( TaskConfig
       , (String, String)
       )
configuration = do
  ls <- lines <$> anyChar `manyTill` eof
  let (rawCfg, rest) = first unlines $ breakWhen ("---" `isPrefixOf`) ls
  case decodeEither' (BS.pack rawCfg) of
    Left err -> fail $ show err
    Right taskCfg -> do
      let predicates = bimap unlines unlines $ breakWhen ("---" `isPrefixOf`) rest
      pure (taskCfg, predicates)

parseSpec :: Parsec String () Spec
parseSpec = try newPredDeclParser <|> specLine
  where
    specLine =
      (\f g h i -> f . g . h . i)
        <$> localTimeoutAnn
        <*> negativeFlag
        <*> withTreeFlag
        <*> hiddenFlag
        <*> do
          spaces
          q <- terms
          ( do
              char ':' >> optional (char ' ')
              queryWithAnswers q . map (: []) <$> terms
            )
            <|> pure (statementToCheck q)

    newPredDeclParser = do
      void $ string "new"
      spaces
      t <- term
      spaces
      void $ char ':'
      spaces
      desc <- many1 anyChar
      pure $ newPredDecl t desc

    localTimeoutAnn =
      option id $
        localTimeout . read
          <$> between (char '[') (char ']') (many1 digit)
          <* spaces

    negativeFlag = option id $ negative <$ char '-'

    hiddenFlag =
      option id $
        char '!'
          >> hidden
            <$> option "" (try (between (char '(') (char ')') description))

    withTreeFlag =
      option id $
        (char '@' >> return withTree)
          <|> (char '#' >> return withTreeNegative)

    description =
      try (between (char '"') (char '"') (descriptionMsg "\""))
        <|> try (between (char '\'') (char '\'') (descriptionMsg "'"))
        <|> descriptionMsg ")"

    descriptionMsg :: String -> Parsec String () String
    descriptionMsg end = many (noneOf end)

defaultOptions :: Requirement -> Spec
defaultOptions = Spec Visible DontShowTree PositiveResult GlobalTimeout

{- FOURMOLU_DISABLE -}
breakWhen :: (a -> Bool) -> [a] -> ([a], [a])
breakWhen p = (takeWhile (not . p) &&& dropWhile (not . p)) >>> second (drop 1)
{- FOURMOLU_ENABLE -}

queryWithAnswers :: [Term] -> [[Term]] -> Spec
queryWithAnswers q as = defaultOptions $ QueryWithAnswers q as

statementToCheck :: [Term] -> Spec
statementToCheck ts = defaultOptions $ StatementToCheck ts

hidden :: String -> Spec -> Spec
hidden s spec = spec {specVisibility = Hidden s}

withTree :: Spec -> Spec
withTree spec = spec {specVisualize = ShowTree}

withTreeNegative :: Spec -> Spec
withTreeNegative = negative . withTree

newPredDecl :: Term -> String -> Spec
newPredDecl t s = defaultOptions $ NewPredDecl t s

negative :: Spec -> Spec
negative spec = spec {specExpection = NegativeResult}

localTimeout :: Int -> Spec -> Spec
localTimeout d spec = spec {specTimeout = LocalTimeout d}
