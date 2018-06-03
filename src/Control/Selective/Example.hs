module Control.Selective.Example where

import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Selective
import Data.Map (Map)

import qualified Data.Map as Map

-- dependencies hello == ["username"]
hello :: Functor f => (String -> f String) -> f String
hello fetch = (\name -> "Hello, " ++ name ++ ".\n") <$> fetch "username"

-- dependencies welcome == ["hostname"]
welcome :: Functor f => (String -> f String) -> f String
welcome fetch = (\name -> "Welcome to " ++ name ++ "!\n") <$> fetch "hostname"

-- dependencies helloAndWelcome == ["hostname", "username"]
helloAndWelcome :: Applicative f => (String -> f String) -> f String
helloAndWelcome fetch = (++) <$> hello fetch <*> welcome fetch

-- dependencies helloAndWelcomeSelective == ["andrey-message", "hostname", "username"]
helloAndWelcomeSelective :: Selective f => (String -> f String) -> f String
helloAndWelcomeSelective fetch = ifS (("Andrey" ==) <$> fetch "username")
    ((++) <$> helloAndWelcome fetch <*> fetch "andrey-message")
    (helloAndWelcome fetch)

fetchIO :: String -> StateT (Map String String) IO String
fetchIO key = do
    maybeValue <- gets (Map.lookup key)
    case maybeValue of
        Nothing -> do
            value <- lift $ do putStr (show key ++ ": "); getLine
            modify $ Map.insert key value
            return value
        Just value -> return value
