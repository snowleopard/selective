-- A little testing framework
module Test where

import Data.List (intercalate)
import System.Exit (exitFailure)
import Test.QuickCheck hiding (Success, Failure, expectFailure)

data Expect = ExpectSuccess | ExpectFailure deriving Eq

data Test = Test String Expect Property

data Tests = Leaf Test | Node String [Tests]

testGroup :: String -> [Tests] -> Tests
testGroup = Node

expectSuccess :: Testable a => String -> a -> Tests
expectSuccess name p = Leaf $ Test name ExpectSuccess (property p)

expectFailure :: Testable a => String -> a -> Tests
expectFailure name p = Leaf $ Test name ExpectFailure (property p)

runTest :: [String] -> Test -> IO ()
runTest labels (Test name expect property) = do
    let label = "[" ++ intercalate "." (reverse labels) ++ "] " ++ name
    result <- quickCheckWithResult (stdArgs { chatty = False }) property
    case (expect, isSuccess result) of
        (ExpectSuccess, True) ->
            putStrLn $ "[OK] " ++ label
        (ExpectFailure, False) ->
            putStrLn $ "[OK, expected failure] " ++ label
        (ExpectFailure, True) ->
            putStrLn $ "[Warning, unexpected success] " ++ label
        (ExpectSuccess, False) -> do
            putStrLn $ "\n[Failure] " ++ label ++ "\n"
            putStrLn $ output result
            exitFailure

runTests :: Tests -> IO ()
runTests = go []
  where
    go labels (Leaf test)        = runTest labels test
    go labels (Node label tests) = mapM_ (go (label : labels)) tests
