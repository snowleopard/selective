{-# LANGUAGE RankNTypes #-}
import Control.Selective.Example

main :: IO ()
main = do
    putStrLn $ "\n\nCyclic dependency graph:\n\n" ++ draw task "B1"
