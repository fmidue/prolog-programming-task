module CodeAnalysis.Rules.SingletonVariablesSpec where

import CodeAnalysis.Helper (shouldDetectProblemsStrict, shouldNotHaveProblems)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Prolog.Programming.CodeAnalysis.Config (emptyCodeAnalysisConfig)
import Prolog.Programming.CodeAnalysis.Types (
  CodeAnalysisConfig (..),
  Severity (..),
  SingletonVariablesConfig (..),
  WithSeverity (..),
 )
import Prolog.Programming.Data (Code)
import Test.Hspec (Spec, describe, it)

caConfig :: CodeAnalysisConfig
caConfig =
  emptyCodeAnalysisConfig {
    singletonVariables =
      SingletonVariablesConfig $ Just $ WithSeverity Hint ()
    }

unmarkedSingletons :: [(Code, [String])]
unmarkedSingletons =
  [ ("p(X,Y) :- q(X).", ["Y"])
  , ("p(X) :- X = [Z|Zs], q(Z).", ["Zs"])
  , ("p(X) :- X = [Z|Zs], q(Zs).", ["Z"])
  , ("p :- a(X).", ["X"])
  , ("p(X) :- a(X), b(Y).", ["Y"])
  , ("p(X,f(Y)) :- g(X).", ["Y"])
  , ("p(A,B).", ["A", "B"])
  , ("p(A,_).", ["A"])
  ]

detectionFree :: [Code]
detectionFree =
  [ "p(X) :- q(X)."
  , "p(X,X)."
  , "p(X) :- X = [Z|Zs], q(Z,Zs)."
  , "p :- a(X), b(X)."
  , "p(X,Y) :- Z is X + Y, q(Z)."
  , "p(X,Y) :- X =:= Y."
  , "p(X,Y) :- X =\\= Y."
  , "p(X,Y) :- not(X =:= Y)."
  , "p(X,Y) :- X \\= Y."
  , "p(X,Y) :- X > Y."
  , "p(X,X,X)."
  , "p(X,X,X,X)."
  , "p(_)."
  , "p(_,_)."
  ]

spec :: Spec
spec = describe "NoSingletonVariables" $ do
  describe "Should detect unmarked singleton variables" $
    forM_ unmarkedSingletons $ \(programCode, unmarked) ->
      it programCode $
        shouldDetectProblemsStrict
          caConfig
          (map (\v -> isInfixOf $ "includes the singleton variable " ++ v) unmarked)
          programCode
  describe "Should not detect any problems" $
    forM_ detectionFree $ \programCode ->
      it programCode $
        shouldNotHaveProblems
          caConfig
          programCode
