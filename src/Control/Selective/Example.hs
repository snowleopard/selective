{-# LANGUAGE ConstraintKinds, GADTs, RankNTypes #-}
module Control.Selective.Example where

import Algebra.Graph
import Algebra.Graph.Export.Dot
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Selective
import Data.Map (Map)

import qualified Data.Map as Map
import qualified Data.Set as Set

task :: Task Selective String Integer
task fetch "B1" = Just $ ifS ((1==) <$> fetch "C1") (fetch "B2") (fetch "A2")
task fetch "B2" = Just $ ifS ((1==) <$> fetch "C1") (fetch "A1") (fetch "B1")
task _     _    = Nothing

-- dependencies login "hello"   == ["username"]
-- dependencies login "welcome" == ["hostname"]
-- dependencies login "both"    == ["hostname", "username"]
-- dependencies login "andrey"  == ["andrey-message", "hostname", "username"]
login :: Task Selective String String
login fetch "hello"   = Just $ (\name -> "Hello, " ++ name ++ ".\n") <$> fetch "username"
login fetch "welcome" = Just $ (\name -> "Welcome to " ++ name ++ "!\n") <$> fetch "hostname"
login fetch "both"    = Just $ (++) <$> fetch "hello" <*> fetch "welcome"
login fetch "andrey"  = Just $ ifS (("Andrey" ==) <$> fetch "username")
    ((++) <$> fetch "both" <*> fetch "andrey-message") (fetch "both")
login _ _ = Nothing

fetchIO :: String -> StateT (Map String String) IO String
fetchIO key = do
    maybeValue <- gets (Map.lookup key)
    case maybeValue of
        Nothing -> do
            value <- lift $ do putStr (show key ++ ": "); getLine
            modify $ Map.insert key value
            return value
        Just value -> return value

graph :: Ord k => (k -> [k]) -> k -> Graph k
graph deps key = transpose $ overlays [ star k (deps k) | k <- keys Set.empty [key] ]
  where
    keys seen []   = Set.toList seen
    keys seen (x:xs)
        | x `Set.member` seen = keys seen xs
        | otherwise           = keys (Set.insert x seen) (deps x ++ xs)

draw :: Task Selective String v -> String -> String
draw task = exportAsIs . graph (dependencies task)

---------------------------------- Validation ----------------------------------

fetch :: Read a => String -> IO a
fetch prompt = do putStr (prompt ++ ": "); read <$> getLine

type Radius = Int
type Width  = Int
type Height = Int

data Shape = Circle Radius | Rectangle Width Height deriving Show

-- Some validation examples:
--
-- > shape (Success True) (Success 10) (Failure ["no width"]) (Failure ["no height"])
-- > Success (Circle 10)
--
-- > shape (Success False) (Failure ["no radius"]) (Success 20) (Success 30)
-- > Success (Rectangle 20 30)
--
-- > shape (Success False) (Failure ["no radius"]) (Success 20) (Failure ["no height"])
-- > Failure ["no height"]
--
-- > shape (Failure ["no choice"]) (Failure ["no radius"]) (Success 20) (Failure ["no height"])
-- > Failure ["no choice"]
shape :: Selective f => f Bool -> f Radius -> f Width -> f Height -> f Shape
shape s r w h = ifS s (Circle <$> r) (Rectangle <$> w <*> h)
