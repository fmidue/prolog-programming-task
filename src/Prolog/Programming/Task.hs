{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Prolog.Programming.Task where

import qualified Text.RawString.QQ                as RS (r)

import Prolog.Programming.Data

import Control.Arrow                    ((>>>), (&&&), second)
import Control.Monad                    (forM, void, when)
import Control.Monad.Random.Class       (MonadRandom)
import Control.Monad.Trans              (MonadIO (liftIO))
import Control.Exception                (evaluate)
import Data.ByteString                  (ByteString)
import Data.List                        ((\\), intercalate, isPrefixOf, nub)
import Data.Maybe                       (catMaybes, fromMaybe, isNothing)
import Data.Either                      (partitionEithers)
import Data.Text.Lazy                   (pack)
import Language.Prolog                  (
  Atom, Clause (..), Goal, Program, Term (..), Unifier, VariableName (..),
  apply, consultString, lhs, term, terms,
  )
import Language.Prolog.GraphViz (Graph, asInlineSvg, resolveFirstTree, resolveTree)
import Text.Parsec                      hiding (Ok)
import Text.PrettyPrint.Leijen.Text (
  Doc, (<+>), hsep, nest, parens, text, vcat, (<$$>), empty,
  )
import System.Random.Shuffle            (shuffleM)
import System.Timeout                   (timeout)
import Data.List.NonEmpty (NonEmpty(..))

exampleConfig :: Config
exampleConfig = Config
  [RS.r|/* % comments for test cases have to start with an extra %
 * % timeout per test in ms (defaults to 10000, only the first timeout is used)
 * Global timeout: 10000
 * % prefixing a test with [<time out in ms>] sets a local timeout for that test
 * a_predicate(Foo,Bar): a_predicate(expected_foo1,expected_bar1), a_predicate(expected_foo2,expected_bar2)
 * a_statement_that_has_to_be_true
 * !a_predicate_whose_answers_are_hidden(Foo,Bar): a_predicate(expected_foo1,expected_bar1), a_predicate(expected_foo2,expected_bar2)
 * !a_hidden_statement_that_has_to_be_true
 * !(<description>) a_hidden_statement_that_has_to_be_true_with_a_description_shown_on_failure
 * @a_test_with_resolution_tree(X) % Only shown if test fails.
 * -a_statement_that_has_to_be_false % also works for all other test statements given above
 * % when combining multiple flags the order has to be <timeout><negative><tree><hidden><space>*<test>
 * new a_predicate_to_define(X): predicate description
 *    % require the definition of a predicate with a user choosen name. Use a_predicate_to_define to refer this predicate in other tests.
 *    % New predicates will be mapped to required predicates in the order they are defined.
 *    % (The initial solution automatically provides comments helping the user with the correct ordering.)
 */
/* Everything from here on (up to an optional hidden section separated by a line of 3 or more dashes)
 * will be part of the visible exercise description (In other words: Only the first comment block is special).
 *
 * You can add as many tests as you like, but keep Autotool's time limit in mind. Additionally, every test has its own time limit,
 * so if one of your tests does not terminate (soon enough) this will be reported as a failure (mentioning the timeout).
 *
 * In this visible part, you can place the explanation of the exercise and all facts & clauses you want to give to the student.
 */
a_fact.
a_clause(Foo) :- a_clause(Foo).
a_dcg_rule --> a_dcg_rule, [terminal1, terminal2], { prolog_term }.
a_test_with_resolution_tree(left_branch) :- fail. % See test line 5
a_test_with_resolution_tree(right_branch) :- fail. % See test line 5
/*
 * The program text will be concatenated with whatever the student submits.
 */
------------------------------
/*
 * This is also part of the program, but is not presented to the student.
 *
 * Be careful to avoid naming clashes to not confuse the student with error messages about code they can't see.
 */
  |]

verifyConfig :: MonadFail m => Config -> m ()
verifyConfig (Config cfg) =
  either (fail . show) (\_ -> return ()) $ parseConfig cfg

describeTask :: Config -> Doc
describeTask (Config cfg) = text . pack $ either
  (const "Error in task configuration!")
  (\(_,_,(visible_facts,_)) -> visible_facts)
  (parseConfig cfg)

initialTask :: Config -> Code
initialTask (Config cfg) = Code $
  if null newDecls then "" else
    foldr (\(Spec _ _ _ _ (NewPredDecl _ desc)) s ->
             "% Define predicate for '" ++ desc
             ++ "' below this line\n \n\n" ++ s)
      "% Any additional definitions can go below this line"
      newDecls
  where
    Right (_,specs,_) = parseConfig cfg
    newDecls = filter isNewPredDecl specs

checkTask
  :: (MonadIO m, MonadRandom m)
  => (forall a . Doc -> m a)
  -> (Doc -> m ())
  -> (ByteString -> m ())
  -> Config
  -> Code
  -> m ()
checkTask reject inform drawPicture (Config cfg) (Code input) = do
  let drawTree tree = do
        svg <- liftIO $ asInlineSvg tree
        drawPicture svg
  let Right (globalTO,specs,(visible_facts,hidden_facts)) = parseConfig cfg
      facts = visible_facts ++ "\n" ++ hidden_facts

  case consultString input of
    Left err -> reject . text . pack $ show err
    Right inProg -> do
      newDefs <- case findNewPredicateDefs specs inProg of
        Left err -> [] <$ (reject . text $ pack err)
        Right newDefs -> pure newDefs
      let newFacts = connectNewDefsAndTests newDefs
          newSpecs = useFoundDefs newDefs specs
      when (requiresNewPredicates specs) $
        inform $ vcat $
          text "Using the following definitions for required predicates:" :
          [ text . pack $ desc ++ ": " ++ tr | (_,tr,desc) <- newDefs]

      case consultString facts of
        Left err -> reject . text . pack $ show err
        Right factProg -> do
          let p = factProg ++ inProg ++ newFacts
          let expect PositiveResult = id
              expect NegativeResult = not
              treeValue DontShowTree _ = Nothing
              treeValue ShowTree t = Just t
              check (Spec _ t r _ (QueryWithAnswers query expected)) =
                case solutions p query of
                  Right (actual,_)
                    | expect r (applySolutions actual query =~= expected)
                    -> Ok
                  Right (actual, tree)
                    -> Wrong (treeValue t tree) actual
                  Left err
                    -> ErrorMsg err
              check (Spec _ t r _ (StatementToCheck query)) =
                case firstSolution p query of
                  Right (actual,tree)
                    | expect r (isNothing actual)
                    -> Wrong (treeValue t tree) (maybe [] pure actual)
                  Right _
                    -> Ok
                  Left err
                    -> ErrorMsg err
              check (Spec _ _ _ _ NewPredDecl{}) = Ok -- test are already insterted elsewhere

              checkWithTimeout s@(Spec _ _ _ to _) = do
                res <- case to of
                  GlobalTimeout -> do
                    timeout (mili2microSec globalTO) $ evaluate (check s)
                  LocalTimeout d -> do
                    timeout (mili2microSec d) $ evaluate (check s)
                pure $ fromMaybe Timeout res
              mili2microSec = (* 1000)

          testCases <- reorderTests newSpecs
          testResult <- liftIO $ runTests testCases checkWithTimeout

          case testResult of
            (Finished AllOk,_) -> inform $ text "ok"
            (Finished (SomeTimeouts (t :| ts)),_) -> do
              inform (text "No.")
              inform $ indent $
                hsep [describeSpec t, text "*appears to be non-terminating* (test case timeout)"]
                <$$> if not (null ts) then text (pack $ show (length ts) ++ " additional test cases also timed out") else empty
            (Aborted reason,(passed,notRun)) -> do
              inform $ vcat
                [ text "No."
                , text "The following test case failed:"]
              explainResultWith inform drawTree reason
              reject (text . pack $
                "tests passed: " ++ show passed
                ++ if notRun > 0 -- only show remaining tests if there is at least one test that was not run
                   then ", tests not run: " ++ show notRun
                   else "")

explainResultWith
  :: Monad m
  => (Doc -> m ())
  -> (Graph -> m ())
  -> AbortReason Spec [Unifier]
  -> m ()
explainResultWith inform drawTree = explainResult
  where
    explainResult (OnErrorMsg x msg)
      = inform $ indent $ vcat
        [describeSpec x
        ,indent $ vcat [text "The following error occurred:",text $ pack msg]
        ]
    explainResult (OnWrong x@(Spec (Hidden _) _ _ _ _) _ _)
      = inform $ indent $ describeSpec x
    explainResult (OnWrong x Nothing actual)
      = inform $ indent $ vcat
        [describeSpec x
        ,indent $ vcat [text "Your submission gives:",
                        indent . text . pack $ printResult actual]
        ]
    explainResult (OnWrong x (Just tree) actual)
      = do
        inform $ indent $ vcat
          [describeSpec x
          ,indent $ vcat [text "Your submission gives:",
                          indent . text . pack $ printResult actual]
          ,indent $ text "derivation tree:"]
        drawTree tree

indent :: Doc -> Doc
indent = nest 4

{-|
pretty-print the interpreter result
-}
printResult :: [Unifier] -> String
printResult [] = "false"
printResult [[]] = "true"
printResult us = intercalate ";\n" $
  map (intercalate ", " . map (\(x,t) -> show x ++ " = " ++ show t)) (nub us)

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
  "The result of the query " ++ showQuery query ++ " is incorrect."

showQuery :: Show a => [a] -> String
showQuery query = "?- " ++ intercalate ", " (map show query) ++ "."

data TestResult res
  = Ok
  | Wrong (Maybe Graph) res
  | ErrorMsg String
  | Timeout

isOk :: TestResult res -> Bool
isOk Ok = True
isOk _ = False

data TestSuiteResult a res
  = Finished (AreAllOk a)
  | Aborted (AbortReason a res)

data AreAllOk a
  = AllOk
  | SomeTimeouts (NonEmpty a)

data AbortReason a res
  = OnWrong a (Maybe Graph) res
  | OnErrorMsg a String

{- |
run a sequence of tests until the first error
returns the result and the test that produced the error
additionally the number of passed tests and tests that were not run is returned
(timeout are not counted as errors unless no other error occurs)
-}
runTests
  :: Monad m
  => [a]
  -> (a -> m (TestResult r))
  -> m (TestSuiteResult a r, (Int,Int))
runTests = runTests' 0 []
  where
    runTests' n [] [] _ = pure (Finished AllOk, (n,0))
    runTests' n (t:ts) [] _ = pure (Finished $ SomeTimeouts (t :| ts), (n,0))
    runTests' n ts (x:xs) check = do
      res <- check x
      case res of
        Ok -> runTests' (n+1) ts xs check
        Wrong g r -> pure (Aborted $ OnWrong x g r, (n,length xs))
        ErrorMsg msg -> pure (Aborted $ OnErrorMsg x msg, (n,length xs))
        Timeout -> runTests' n (x:ts) xs check

(=~=) :: [[Term]] -> [[Term]] -> Bool
actual =~= expected =
  nub actual `isSublistOf` nub expected
  && nub expected `isSublistOf` nub actual
  where
    isSublistOf xs ys = null (xs \\ ys)

solutions :: Program -> [Goal] -> Either String ([Unifier], Graph)
solutions = resolveTree

firstSolution :: Program -> [Goal] -> Either String (Maybe Unifier, Graph)
firstSolution = resolveFirstTree

applySolutions :: [Unifier] -> [Goal] -> [[Term]]
applySolutions xs q = map (\s -> map (apply s) q) xs

reorderTests :: MonadRandom m => [Spec] -> m [Spec]
reorderTests = shuffleConcat . classify
  where
    shuffleConcat
      :: MonadRandom m
      => (([Spec],[Spec],[Spec],[Spec],[Spec]),[Spec])
      -> m [Spec]
    shuffleConcat ((xs1,xs2,xs3,xs4,xs5),xs6) = do
      ys1 <- shuffleM xs1
      ys2 <- shuffleM xs2
      ys3 <- shuffleM xs3
      ys4 <- shuffleM xs4
      ys5 <- shuffleM xs5
      ys6 <- shuffleM xs6
      pure $ ys1 ++ ys2 ++ ys3 ++ ys4 ++ ys5 ++ ys6
    -- there is no Monoid instance for 6-tuples for some reason,
    -- so we use nested tuples instead
    -- results in a tuple (non-hidden, hidden)
    -- with non-hiden =
    -- (positiveWithTree,negativeWithTree,positiveNoTree,negativeNoTree,queries)
    classify :: [Spec] -> (([Spec],[Spec],[Spec],[Spec],[Spec]),[Spec])
    classify = mconcat . map classify'
    classify' :: Spec -> (([Spec],[Spec],[Spec],[Spec],[Spec]),[Spec])
    classify' s@(Spec (Hidden _) _ _ _ _)
      = (([],[],[],[],[]),[s])
    classify' s@(Spec Visible _ _ _ QueryWithAnswers{})
      = (([],[],[],[],[s]),[])
    classify' s@(Spec Visible DontShowTree NegativeResult _ _)
      = (([],[],[],[s],[]),[])
    classify' s@(Spec Visible DontShowTree PositiveResult _ _)
      = (([],[],[s],[],[]),[])
    classify' s@(Spec Visible ShowTree NegativeResult _ _)
      = (([],[s],[],[],[]),[])
    classify' s@(Spec Visible ShowTree PositiveResult _ _)
      = (([s],[],[],[],[]),[])

{-| Working with predicates whos name is unknow at configuration time -}
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
  = Right $
    zipWith (\(Spec _ _ _ _ (NewPredDecl tl desc)) tr -> (tl,tr,desc))
      newDecls
      clauseHeads
  where
    newDecls = filter isNewPredDecl specs
    clauseHeads = nub $ termHead . lhs <$> cls

termHead :: Term -> Atom
termHead (Struct h _) = h
termHead _ = error "can't extract clause head"

connectNewDefsAndTests :: [(Term,Atom,String)] -> [Clause]
connectNewDefsAndTests =
  map (\(tl, tr, _) -> Clause tl [Struct tr (Var <$> vars tl)])
  where
    vars (Struct _ ts) = concatMap vars ts
    vars (Var x@VariableName{}) = [x]
    vars (Var Wildcard{}) = []
    vars (Cut _) = []

useFoundDefs :: [(Term,Atom,String)] -> [Spec] -> [Spec]
useFoundDefs ds specs = updateSpec <$> specs
  where
    substitutions = map (\(tl,tr,_) -> (termHead tl,tr)) ds
    updateSpec :: Spec -> Spec
    updateSpec (Spec v t e to r) = Spec v t e to (updateReq r)
    updateReq :: Requirement -> Requirement
    updateReq (NewPredDecl t d) =
      NewPredDecl t d
    updateReq (QueryWithAnswers ts tss) =
      QueryWithAnswers (replaceHead <$> ts) (fmap (fmap replaceHead) tss)
    updateReq (StatementToCheck ts) =
      StatementToCheck $ replaceHead <$> ts
    replaceHead :: Term -> Term
    replaceHead (Struct h ts) =
      case lookup h substitutions of
        Just r -> Struct r (replaceHead <$> ts)
        Nothing -> Struct h (replaceHead <$> ts)
    replaceHead t = t

{- * Config parser -}

parseConfig
  :: String
  -> Either ParseError (TimeoutDuration, [Spec], (String, String))
parseConfig = parse configuration "(config)"

type TimeoutDuration = Int

configuration :: Parsec String () (TimeoutDuration, [Spec], (String, String))
configuration = (\(d,xs) s -> (d,xs,s)) <$> specification <*> sourceText

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

specification :: Parsec String () (TimeoutDuration,[Spec])
specification = do
  let specLine = ((\f g h i -> f . g . h . i)
                  <$> localTimeoutAnn
                  <*> negativeFlag
                  <*> withTreeFlag
                  <*> hiddenFlag) <*> do
        spaces
        q <- terms
        (do char ':' >> optional (char ' ')
            queryWithAnswers q . map (:[]) <$> terms)
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
      globalTimeout = do
        void $ string "Global timeout:"
        spaces
        read <$> many1 digit
  lines' <- commentBlock
  let parseSpecLine (i, s) = parse
        ((Nothing <$ commentLine)
         <|> (Just <$> ((Left <$> try globalTimeout)
                        <|> Right <$> (try newPredDeclParser
                                       <|> specLine))))
        ("Specification line " ++ show i) s
  timeoutAndSpecs <- zip [1 :: Integer ..] lines' `forM` \t ->
   case parseSpecLine t of
      Right spec -> return spec
      Left err   -> fail (show err)
  let (timeouts,specs) = partitionEithers $ catMaybes timeoutAndSpecs
      timeout' = if null timeouts then 10000 else head timeouts
  pure (timeout', specs)
  where
    localTimeoutAnn = option id $
      localTimeout . read
      <$> between (char '[') (char ']') (many1 digit) <* spaces
    negativeFlag = option id $ negative <$ char '-'
    hiddenFlag   = option id $
      char '!' >> hidden
      <$> option "" (try (between (char '(') (char ')') (many $ noneOf ")")))
    withTreeFlag = option id $ (char '@' >> return withTree)
                           <|> (char '#' >> return withTreeNegative)

commentLine :: Parsec String u String
commentLine = spaces >> char '%' >> many anyChar

commentBlock :: Parsec String u [String]
commentBlock = do
  let startMarker =            string "/* "
  let separator   = endOfLine >> string " * "
  let endMarker   = endOfLine >> string " */"
  let line = many $ do notFollowedBy separator
                       notFollowedBy endMarker
                       anyToken
  between startMarker endMarker $ line `sepBy` try separator

sourceText :: Parsec String u (String, String)
sourceText = do
  ls <- lines <$> anyChar `manyTill` eof
  let (visiblePart, hiddenPart) = breakWhen ("---" `isPrefixOf`) ls
  return (unlines visiblePart, unlines hiddenPart)

breakWhen :: (a -> Bool) -> [a] -> ([a],[a])
breakWhen p = (takeWhile (not . p) &&& dropWhile (not . p)) >>> second (drop 1)
