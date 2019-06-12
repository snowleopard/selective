{-# LANGUAGE GADTs #-}
module Query where

import Control.Selective
import Data.List

type Prompt = String

data Query a where
    Terminal :: Prompt   -> Query String
    File     :: FilePath -> Query String
    Pure     :: a -> Query a
    Apply    :: Query (a -> b) -> Query a -> Query b
    Select   :: Query (Either a b) -> Query (a -> b) -> Query b

instance Functor Query where
    fmap f x = Apply (Pure f) x

instance Applicative Query where
    pure  = Pure
    (<*>) = Apply

instance Selective Query where
    select = Select

pureQuery :: Query String
pureQuery = (++) <$> pure "Hello " <*> pure "World!"

replace :: String -> String -> String -> String
replace [] _ xs = xs
replace from to xs | Just xs <- stripPrefix from xs = to ++ replace from to xs
replace from to (x:xs) = x : replace from to xs
replace _ _ [] = []

welcomeQuery :: Query String
welcomeQuery = replace "[NAME]" <$> Terminal "Name" <*> File "welcome.txt"

welcomeBackQuery :: Query String
welcomeBackQuery = (++) <$> welcomeQuery <*> pure "It's great to have you back!\n"

welcomeQuery2 :: Query String
welcomeQuery2 =
    ifS (isInfixOf <$> Terminal "Name" <*> File "past-participants.txt")
        welcomeBackQuery
        welcomeQuery

getPure :: Query a -> Maybe a
getPure (Terminal _) = Nothing
getPure (File _) = Nothing
getPure (Pure a) = Just a
getPure (Apply f x) = do
    pf <- getPure f
    px <- getPure x
    return (pf px)
getPure (Select x y) = do
    px <- getPure x
    py <- getPure y
    return (either py id px)

getEffects :: Query a -> ([Prompt], [FilePath])
getEffects (Terminal p) = ([p], [] )
getEffects (File f) = ([] , [f])
getEffects (Pure _) = ([] , [] )
getEffects (Apply f x) = (p1 ++ p2, f1 ++ f2)
  where
    (p1, f1) = getEffects f
    (p2, f2) = getEffects x
getEffects (Select x y) = (px ++ py, fx ++ fy)
  where
    (px, fx) = getEffects x
    (py, fy) = getEffects y
