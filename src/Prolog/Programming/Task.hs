{-# HLINT ignore "Use unless" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ViewPatterns #-}
module Prolog.Programming.Task (
  checkTask,
  exampleConfig,
  verifyConfig,
  describeTask,
  initialTask,
) where

import Prolog.Programming.Data
import Prolog.Programming.ExampleConfig
import Prolog.Programming.Helper        (termHead)
import Prolog.Programming.Parser
import Prolog.Programming.TestRunner
import Prolog.Programming.TestSpec

import Control.Monad                    (when, zipWithM)
import Control.Monad.Random.Class       (MonadRandom)
import Control.Monad.Trans              (MonadIO (liftIO))

import Data.ByteString                  (ByteString)
import Data.Either                      (fromRight)
import Data.List                        (intercalate, nub)
import Data.List.NonEmpty               (NonEmpty(..))
import Data.Maybe                       (mapMaybe)
import Data.Text.Lazy                   (pack)
import Data.Void                        (absurd)

import Language.Prolog                  (
  Atom, Clause (..), Program, Term (..), Unifier, consultString, lhs,
  )
import Language.Prolog.GraphViz (Graph, asInlineSvgWith)
import Language.Prolog.GraphViz.Formatting (GraphFormatting, queryStyle, resolutionStyle)

import Text.Parsec (ParseError)
import Text.PrettyPrint.Leijen.Text (
  Doc, (<+>), nest, parens, text, vcat, empty, line, align, (<$$>),
  )

verifyConfig :: MonadFail m => Config -> m ()
verifyConfig (Config cfg) =
  either (fail . show) (\_ -> return ()) $ parseConfig cfg

describeTask :: Config -> Doc
describeTask (Config cfg) = text . pack $ either
  (const "Error in task configuration!")
  (\(_,_,_,_,_,_,(visible_facts,_)) -> visible_facts)
  (parseConfig cfg)

initialTask :: Config -> Code
initialTask (Config cfg) = Code $
  if null newDecls then "" else
    foldr (\desc s ->
             "% Define predicate for '" ++ desc
             ++ "' below this line\n \n\n" ++ s)
      "% Any additional definitions can go below this line"
      newDecls
  where
    (_,_,_,_,_,specs,_) = parseConfig cfg `orError` "config should have been validated earlier"
    newDecls = mapMaybe (\(Spec _ _ _ _ r) -> newPredDesc r) specs
    newPredDesc (NewPredDecl _ desc) = Just desc
    newPredDesc StatementToCheck{} = Nothing
    newPredDesc QueryWithAnswers{} = Nothing

orError :: Either a b -> String -> b
orError x str = fromRight (error str) x

checkTask
  :: (MonadIO m, MonadRandom m)
  => (forall a . Doc -> m a)
  -> (Doc -> m ())
  -> (ByteString -> m ())
  -> Config
  -> Code
  -> m ()
checkTask reject inform drawPicture (Config cfg) (Code input) = do
  let (globalTO,treeStyle,includeTask,includeHidden,allowListMatching,specs,(visible_facts,hidden_facts))
        = parseConfig cfg `orError` "config should have been validated earlier"
      drawTree tree = do
        svg <- liftIO $ asInlineSvgWith (grabFormatting treeStyle) tree
        drawPicture svg

  case consultString input of
    Left err -> reject . text . pack $ show err
    Right inProg -> do

      when (not allowListMatching) $
        case containsHeadTailPattern inProg of
          Nothing -> pure ()
          Just t -> reject . text . pack $ "forbidden use of head/tail-list-matching in " ++ show t

      newDefs <- case findNewPredicateDefs specs inProg of
        Left err -> [] <$ (reject . text $ pack err)
        Right newDefs -> pure newDefs

      when (requiresNewPredicates specs) $
        inform $ vcat $
          text "Using the following definitions for required predicates:" :
          [ text . pack $ desc ++ ": " ++ tr | (_,tr,desc) <- newDefs]

      case consultStringsAndFilter visible_facts (taskFilter includeTask inProg) hidden_facts (hiddenFilter includeHidden inProg) of
        Left err -> reject . text . pack $ show err
        Right factProg -> do
          testResult <- liftIO $ testRunner globalTO factProg inProg specs newDefs
          case testResult of
            (Finished AllOk,(passed,_)) ->
              inform $ vcat
                [ text "Ok"
                , text (pack $ unwords [show passed, plural passed "test was" "tests were", "run"])
                ]
            (Finished (SomeTimeouts (t :| ts)),(passed,_)) -> do
              let testsRun = passed + 1 + length ts
              reject $ vcat
                [ text "No."
                , text (pack $ unwords [show testsRun, plural testsRun "test was" "tests were", "run"])
                ] <> nested
                  (line <> describeSpec t
                    <> nested (line <> text "*it appears to be non-terminating* (test case timeout)")
                    <> line <> if not (null ts)
                      then text (pack $ show (length ts) ++ " additional test "++ plural (length ts) "case" "cases"++" also timed out")
                      else empty
                  )
            (Aborted reason,(passed,notRun)) -> do
              let (reasonDoc,mTree) = explainReason reason
              inform $ vcat
                [ text "No."
                , text (pack $ unwords [show (passed+1), plural (passed+1) "test was" "tests were", "run"])
                , text "The following test case failed:"
                ] <> reasonDoc
              maybe (pure ()) drawTree mTree
              reject (text . pack $
                "tests passed: " ++ show passed
                ++ if notRun > 0 -- only show remaining tests if there is at least one test that was not run
                   then ", tests not run: " ++ show notRun
                   else "")

consultStringsAndFilter :: String -> (Clause -> Bool) -> String -> (Clause -> Bool) -> Either ParseError [Clause]
consultStringsAndFilter visibleDefs keepVisible hiddenDefs keepHidden = do
  vs <- consultString visibleDefs
  hs <- consultString hiddenDefs
  pure $ filter keepVisible vs ++ filter keepHidden hs

taskFilter :: IncludeTask -> Program -> Clause -> Bool
taskFilter Yes _ = const True
taskFilter No{} _ = const False
taskFilter Filtered prog = \clause -> not $ any ((Just True ==) . compareClause clause) prog
  where
    compareClause :: Clause -> Clause -> Maybe Bool
    compareClause (Clause p xs) (Clause q ys) = Just $ p == q && xs == ys
    compareClause _ _ = Nothing

hiddenFilter :: IncludeHidden -> Program -> Clause -> Bool
hiddenFilter Yes _ = const True
hiddenFilter (No x) _ = absurd x
hiddenFilter Filtered prog = notDefinedByProg
  where
    notDefinedByProg :: Clause -> Bool
    notDefinedByProg x = case extractPredicate $ lhs x of
      Just (p,k) -> (p,k) `notElem` inputDefs
      Nothing -> error "impossible"
    inputDefs :: [(Atom,Int)]
    inputDefs = mapMaybe (extractPredicate . lhs) prog
    extractPredicate :: Term -> Maybe (Atom,Int)
    extractPredicate (Struct p (length -> k)) = Just (p,k)
    extractPredicate (Var _) = Nothing
    extractPredicate (Cut _) = Nothing

plural :: (Eq a, Num a) => a -> b -> b -> b
plural 1 x _ = x
plural _ _ y = y

explainReason :: AbortReason Spec (Maybe [Unifier]) -> (Doc, Maybe Graph)
explainReason = explainResult
  where
    explainResult (OnErrorMsg x msg)
      = (nested $ line <> vcat
        [describeSpec x
        , text "The following error occurred:" <> nested (line <> text (pack msg))
        ]
        , Nothing)
    explainResult (OnWrong x@(Spec (Hidden _) _ _ _ _) _ _)
      = (nested $ line <> describeSpec x, Nothing)
    explainResult (OnWrong x mTree mActual)
      = (nested $
          line <> describeSpec x
          <$$> resultMsg mActual
            <> treeMsg mTree
        , mTree)

treeMsg :: Maybe Graph -> Doc
treeMsg = maybe empty (const (line <> text "Derivation tree:"))

resultMsg :: Maybe [Unifier] -> Doc
resultMsg Nothing =
  text "Your submission is not general enough."
  <$$> text "(Your program does not work correctly on arbitrary data.)"
resultMsg (Just actual) =
  text "Your" <> align
    (text " submission gives:"
    <$$> if null actual then text "false" else (vcat . map (text . pack . printUnifier)) actual)

nested :: Doc -> Doc
nested = nest 4

{-|
pretty-print the interpreter result
-}
-- printResult :: [Unifier] -> String
-- printResult [] = "false"
-- printResult us = intercalate ";\n" $
--   map printUnifier $ nub us

printUnifier :: Unifier -> String
printUnifier [] = "true"
printUnifier xs = intercalate ", " $ map (\(x,t) -> show x ++ " = " ++ show t) xs

describeSpec :: Spec -> Doc
describeSpec (Spec (Hidden str) _ _ _ _) = text . pack $
  "(a hidden test" ++ str ++")"
describeSpec (Spec Visible _ e _ (StatementToCheck query)) =
  text (pack $ showQuery query)
  <+> parens (text (pack "expected") <+> describeExp e)
  where
    describeExp PositiveResult = text "a positive result"
    describeExp NegativeResult = text "false"
describeSpec (Spec Visible _ _ _ (QueryWithAnswers query _)) = text . pack $
  "The result of the query " ++ show (showQuery query) ++ " is incorrect."
describeSpec (Spec Visible _ _ _ (NewPredDecl _ _)) = error "NewPredDecl should not be passed to describeSpec"

showQuery :: Show a => [a] -> String
showQuery query = "?- " ++ intercalate ", " (map show query) ++ "."

{-| Working with predicates whose name is unknown at configuration time -}
isNewPredDecl :: Spec -> Bool
isNewPredDecl (Spec _ _ _ _ NewPredDecl{}) = True
isNewPredDecl _ = False

requiresNewPredicates :: [Spec] -> Bool
requiresNewPredicates = any isNewPredDecl

findNewPredicateDefs :: [Spec] -> [Clause] -> Either String [(Term,Atom,String)]
findNewPredicateDefs specs cls
  | length newDecls > length clauseHeads
  = Left "Not all required predicates defined"
  | otherwise
  = zipWithM match
      newDecls
      clauseHeads
  where
    newDecls = mapMaybe extractNewDeclArgs specs
    extractNewDeclArgs (Spec _ _ _ _ (NewPredDecl tl desc)) = Just (tl,desc)
    extractNewDeclArgs (Spec _ _ _ _ QueryWithAnswers{}) = Nothing
    extractNewDeclArgs (Spec _ _ _ _ StatementToCheck{}) = Nothing

    clauseHeads = nub $ termHead . lhs <$> cls

    match :: (Term,String) -> (Atom,Int) -> Either String (Term,Atom,String)
    match (tl@(Struct _ args) ,desc) (tr,ar)
      | expectedAr /= ar = Left $ unlines $ map unwords
        [ ["Definition for",desc,"does not have the correct arity."]
        , ["Expected a predicate with",show expectedAr, plural expectedAr "argument," "arguments," ,"but",show tr, "has", show ar++"."]
        ]
      | otherwise = Right (tl,tr,desc)
      where expectedAr = length args
    match _ _ = error "can't match definitions: term is not a predicate"

grabFormatting :: TreeStyle -> GraphFormatting
grabFormatting QueryStyle = queryStyle
grabFormatting ResolutionStyle = resolutionStyle

containsHeadTailPattern :: Program -> Maybe Clause
containsHeadTailPattern [] = Nothing
containsHeadTailPattern (clause@(Clause hd gs) : cls) =
  case hasHeadTailPattern hd <> mconcat (map hasHeadTailPattern gs) of
    PatternFound -> Just clause
    DontKnow -> containsHeadTailPattern cls
containsHeadTailPattern (ClauseFn{} : cls) = containsHeadTailPattern cls

hasHeadTailPattern :: Term -> HasHeadTailPattern
hasHeadTailPattern (Struct "." [_,Var _]) = PatternFound
hasHeadTailPattern (Struct _ xs) = mconcat $ map hasHeadTailPattern xs
hasHeadTailPattern Var{} = DontKnow
hasHeadTailPattern Cut{} = DontKnow

data HasHeadTailPattern = PatternFound | DontKnow

instance Semigroup HasHeadTailPattern where
  PatternFound <> _ = PatternFound
  DontKnow <> x = x

instance Monoid HasHeadTailPattern where
  mempty = DontKnow
