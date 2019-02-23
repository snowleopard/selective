{-# LANGUAGE ConstraintKinds, DeriveFunctor, GADTs, RankNTypes #-}
module Control.Selective.Parser where

import Control.Applicative
import Control.Monad
import Control.Selective

newtype Parser a = Parser { parse :: String -> [(a, String)] }

instance Functor Parser where
    fmap f p = Parser $ \x -> [ (f a, s) | (a, s) <- parse p x ]

instance Applicative Parser where
    pure a = Parser $ \s -> [(a, s)]
    (<*>)  = ap

instance Alternative Parser where
    empty   = Parser $ \_ -> []
    p <|> q = Parser $ \s -> parse p s ++ parse q s

instance Selective Parser where
    select = selectM

instance Monad Parser where
    return = pure
    p >>= f = Parser $ \x -> concat [ parse (f a) y | (a, y) <- parse p x ]

class MonadZero f where
    zero :: f a

instance MonadZero Parser where
    zero = Parser (\_ -> [])

item :: Parser Char
item = Parser $ \s -> case s of
    ""    -> []
    (c:cs) -> [(c,cs)]

sat :: (Char -> Bool) -> Parser Char
sat p = do { c <- item; if p c then return c else zero }

char :: Char -> Parser Char
char c = sat (==c)

string :: String -> Parser String
string []     = return ""
string (c:cs) = do
    _ <- char c
    _ <- string cs
    return (c:cs)

bin :: Parser Int
bin = undefined

hex :: Parser Int
hex = undefined

numberA :: Parser Int
numberA = (string "0b" *> bin) <|> (string "0x" *> hex)

numberS :: Parser Int
numberS = ifS ((=='b') <$> (string "0" *> sat (`elem` "bh"))) bin hex
