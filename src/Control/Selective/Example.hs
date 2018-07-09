{-# LANGUAGE ConstraintKinds, GADTs, RankNTypes #-}
module Control.Selective.Example where

import Algebra.Graph
import Algebra.Graph.Export.Dot
import Build.Task
import Control.Selective

import qualified Data.Set as Set

-- dependencies task "B1" = ["A2","B2","C1"]
-- dependencies task "B2" = ["A1","B1","C1"]
-- dependencies task "A1" = []
task :: Tasks Selective String Integer
task "B1" = Just $ Task $ \fetch -> ifS ((1==) <$> fetch "C1") (fetch "B2") (fetch "A2")
task "B2" = Just $ Task $ \fetch -> ifS ((1==) <$> fetch "C1") (fetch "A1") (fetch "B1")
task _    = Nothing

-- dependencies task2 "B1" == ["A1","A2","C5","C6","D5","D6"]
task2 :: Tasks Selective String Integer
task2 "B1" = Just $ Task $ \fetch -> (odd <$> fetch "A1") `bindS` \x ->
                                     (odd <$> fetch "A2") `bindS` \y ->
                                        let c = if x then "C" else "D"
                                            n = if y then "5" else "6"
                                        in fetch (c ++ n)
task2 _    = Nothing

data Key = A Int | B Int | C Int Int deriving (Eq, Show)

editDistance :: Tasks Selective Key Int
editDistance (C i 0) = Just $ Task $ const $ pure i
editDistance (C 0 j) = Just $ Task $ const $ pure j
editDistance (C i j) = Just $ Task $ \fetch ->
    ((==) <$> fetch (A i) <*> fetch (B j)) `bindS` \equals ->
        if equals
            then fetch (C (i - 1) (j - 1))
            else (\insert delete replace -> 1 + minimum [insert, delete, replace])
                 <$> fetch (C  i      (j - 1))
                 <*> fetch (C (i - 1)  j     )
                 <*> fetch (C (i - 1) (j - 1))
editDistance _ = Nothing

graph :: Ord k => (k -> [k]) -> k -> Graph k
graph deps key = transpose $ overlays [ star k (deps k) | k <- keys Set.empty [key] ]
  where
    keys seen []   = Set.toList seen
    keys seen (x:xs)
        | x `Set.member` seen = keys seen xs
        | otherwise           = keys (Set.insert x seen) (deps x ++ xs)

draw :: Tasks Selective String v -> String -> String
draw tasks = exportAsIs . graph deps
  where
    deps k = maybe [] dependencies $ tasks k

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
-- > shape (Success False) (Failure ["no radius"]) (Failure ["no width"]) (Failure ["no height"])
-- > Failure ["no width", "no height"]
--
-- > shape (Failure ["no choice"]) (Failure ["no radius"]) (Success 20) (Failure ["no height"])
-- > Failure ["no choice"]
shape :: Selective f => f Bool -> f Radius -> f Width -> f Height -> f Shape
shape s r w h = ifS s (Circle <$> r) (Rectangle <$> w <*> h)

-- > s1 = shape (Failure ["no choice 1"]) (Failure ["no radius 1"]) (Success 20) (Failure ["no height 1"])
-- > s2 = shape (Success False) (Failure ["no radius 2"]) (Success 20) (Failure ["no height 2"])
-- > twoShapes s1 s2
-- > Failure ["no choice 1","no height 2"]
twoShapes :: Selective f => f Shape -> f Shape -> f (Shape, Shape)
twoShapes s1 s2 = (,) <$> s1 <*> s2
