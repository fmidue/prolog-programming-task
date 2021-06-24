module Prolog.Programming.GraphViz (
  asInlineSvg, resolveWithTree, resolveFirstWithTree,
  ) where

import qualified Data.ByteString                  as B (ByteString, hGetContents)

import Data.GraphViz (
  GraphvizOutput (Svg), commandFor, graphvizWithHandle,
  )
import Language.Prolog (
  Goal, Program, Unifier, resolve_, resolveN_,
  )
import Language.Prolog.GraphViz (
  Graph, runGraphGenT, toDot,
  )

resolveWithTree :: Program -> [Goal] -> Either String ([Unifier], Graph)
resolveWithTree p q = runGraphGenT $ resolve_ p q

resolveFirstWithTree :: Program -> [Goal] -> Either String (Maybe Unifier, Graph)
resolveFirstWithTree p q = do
  (us,t) <- runGraphGenT $ resolveN_ 1 p q
  pure $ case us of
    [] -> (Nothing,t)
    (x:_) -> (Just x,t)

asInlineSvg :: Graph -> IO B.ByteString
asInlineSvg graph =
  graphvizWithHandle (commandFor dot) dot Svg B.hGetContents
  where
    dot = toDot [] graph
