{-# LANGUAGE ConstraintKinds, GADTs, LambdaCase, RankNTypes #-}
module Parser where

import Control.Applicative
import Control.Monad
import Control.Selective

-- See Section 7.2 of the paper: https://dl.acm.org/doi/10.1145/3341694.

newtype Parser a = Parser { parse :: String -> [(a, String)] }

instance Functor Parser where
    fmap f p = Parser $ \x -> [ (f a, s) | (a, s) <- parse p x ]

instance Applicative Parser where
    pure a = Parser $ \s -> [(a, s)]
    (<*>)  = ap

instance Alternative Parser where
    empty   = Parser (const [])
    p <|> q = Parser $ \s -> parse p s ++ parse q s

instance Selective Parser where
    select = selectM

instance Monad Parser where
    return = pure
    p >>= f = Parser $ \x -> concat [ parse (f a) y | (a, y) <- parse p x ]

class MonadZero f where
    zero :: f a

instance MonadZero Parser where
    zero = Parser (const [])

item :: Parser Char
item = Parser $ \case
    ""    -> []
    (c:cs) -> [(c,cs)]

sat :: (Char -> Bool) -> Parser Char
sat p = do { c <- item; if p c then pure c else zero }

char :: Char -> Parser Char
char c = sat (==c)

string :: String -> Parser String
string []     = pure ""
string (c:cs) = do
    _ <- char c
    _ <- string cs
    pure (c:cs)

bin :: Parser Int
bin = undefined

hex :: Parser Int
hex = undefined

numberA :: Parser Int
numberA = (string "0b" *> bin) <|> (string "0x" *> hex)

numberS :: Parser Int
numberS = string "0" *> ifS (('b'==) <$> sat (`elem` "bx")) bin hex
