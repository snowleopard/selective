{-# LANGUAGE RankNTypes #-}
import Control.Selective
import Control.Selective.Example

test :: String -> IO ()
test key = putStrLn $ "dependencies " ++ key ++ " == " ++ show (dependencies login key)

main :: IO ()
main = do
    putStrLn "Test dependencies"
    test "hello"
    test "welcome"
    test "both"
    test "andrey"

    putStrLn $ "\n\nCyclic dependency graph:\n\n" ++ draw task "B1"
