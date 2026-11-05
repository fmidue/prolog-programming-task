module CodeAnalysis.Rules.SymbolOverloadSpec where

import CodeAnalysis.Helper (
  shouldDetectProblemsStrict,
  shouldDetectProblemsStrict',
  shouldNotHaveProblems,
 )
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  Severity (..),
  SymbolOverloadConfig (SymbolOverloadConfig),
  WithSeverity (..),
 )
import Prolog.Programming.Data (Code)
import Test.Hspec (Spec, describe, it)

caConfig :: CodeAnalysisConfig
caConfig =
  emptyCodeAnalysisConfig {
    symbolOverload =
      SymbolOverloadConfig $ Just $ WithSeverity Hint ()
    }

submissionOverloads :: [Code]
submissionOverloads =
  [ "p :- q(p)."
  , "p :- q(p), p."
  , "p :- not(q(p))."
  , "p :- !, q(p)."
  , "p :- (q(p), r)."
  , "p :- (q(p); r)."
  ]

taskPredicateConflicts :: [(Code, Code)]
taskPredicateConflicts =
  [
    ( "check."
    , "r :- (q(check); s)."
    )
  ,
    ( "check(X)."
    , "r :- not(q(check))."
    )
  ]

taskDataConstructorConflicts :: [(Code, Code)]
taskDataConstructorConflicts =
  [
    ( "p(node(leaf))."
    , "node."
    )
  ,
    ( "p :- q(node)."
    , "node."
    )
  ]

detectionFree :: [Code]
detectionFree =
  [ "p(node(leaf))."
  , "p :- q(node(leaf)), r(leaf)."
  , "p :- (q(a); r(b)), not(s(c))."
  ]

spec :: Spec
spec = describe "SymbolOverload" $ do
  describe "detects symbols overloaded in the submission" $
    forM_ submissionOverloads $ \programCode ->
      it programCode $
        shouldDetectProblemsStrict
          caConfig
          [isInfixOf "used interchangeably as a predicate and a data constructor"]
          programCode

  describe "detects task predicates used as data constructors" $
    forM_ taskPredicateConflicts $ \(otherDefinitions, programCode) ->
      it programCode $
        shouldDetectProblemsStrict'
          caConfig
          [isInfixOf "which is used as a data constructor but should really be used as a predicate"]
          programCode
          otherDefinitions

  describe "detects task data constructors used as predicates" $
    forM_ taskDataConstructorConflicts $ \(otherDefinitions, programCode) ->
      it programCode $
        shouldDetectProblemsStrict'
          caConfig
          [isInfixOf "which is used as a predicate but should really be used as a data constructor"]
          programCode
          otherDefinitions

  describe "does not treat ordinary structured arguments as predicates" $
    forM_ detectionFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems caConfig programCode
