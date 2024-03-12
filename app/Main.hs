module Main where

import qualified Data.ByteString as BS

import System.Environment (getArgs)

import Text.PrettyPrint.Leijen.Text ()

import Prolog.Programming.Task
import Prolog.Programming.Data (Config(..),Code(..))

main :: IO ()
main = do
  args <- getArgs
  case args of
    [task, solution] -> do
      config <- Config <$> readFile task
      code <- Code <$> readFile solution
      runMain config code
    _ -> putStrLn "usage test-task-prolog <task> <solution>"

runMain :: Config -> Code -> IO ()
runMain config code = do
  verifyConfig config
  checkTask (fail . show) print writeTreeToDisk config code

writeTreeToDisk :: BS.ByteString -> IO ()
writeTreeToDisk g = BS.writeFile "tree.svg" g >> putStrLn "wrote tree to file://tree.svg"
