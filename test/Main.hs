{-# LANGUAGE RankNTypes #-}
import Control.Selective
import Control.Selective.Example

test :: String -> (forall f. Selective f => (String -> f String) -> f String) -> IO ()
test name x = putStrLn $ "dependencies " ++ name ++ " == " ++ show (dependencies x)

main :: IO ()
main = do
    putStrLn "Test dependencies"
    test "hello"                    hello
    test "helloAndWelcome"          helloAndWelcome
    test "helloAndWelcomeSelective" helloAndWelcomeSelective
