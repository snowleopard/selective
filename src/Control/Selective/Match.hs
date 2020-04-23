{-# LANGUAGE DeriveFunctor, FunctionalDependencies, GADTs, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables, LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Selective.Match
-- Copyright  : (c) Andrey Mokhov 2018-2020
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- This is a library for /selective applicative functors/, or just
-- /selective functors/ for short, an abstraction between applicative functors
-- and monads, introduced in this paper:
-- https://www.staff.ncl.ac.uk/andrey.mokhov/selective-functors.pdf.
--
-- An experiment in expressing Applicative, Selective and Monad using the Match
-- type class.
-----------------------------------------------------------------------------
module Control.Selective.Match where

import Prelude hiding (pure)

-- | A generalised sum type where @t@ stands for the type of constructor "tags".
-- Each tag has a type parameter @x@ which determines the type of the payload.
-- A 'Sigma' @t@ value therefore contains a payload whose type is not visible
-- externally but is revealed when pattern-matching on the tag.
--
-- See 'Two', 'eitherToSigma' and 'sigmaToEither' for an example.
data Sigma t where
    Sigma :: t x -> x -> Sigma t

-- | A data type defining no tags. Similar to 'Data.Void.Void' but parameterised.
data Zero a where

-- | A data type with a single tag. This data type is commonly known as @Refl@,
-- see "Data.Type.Equality".
data One a b where
    One :: One a a

-- | A data type with two tags 'A' and 'B' that allows us to encode the good old
-- 'Either' as 'Sigma' 'Two', where the tags 'A' and 'B' correspond to 'Left'
-- and 'Right', respectively. See 'eitherToSigma' and 'sigmaToEither' that
-- witness the isomorphism between 'Either' @a b@ and 'Sigma' @(@'Two'@ a b)@.
data Two a b c where
    A :: Two a b a
    B :: Two a b b

-- | Encode 'Either' into a generalised sum type.
eitherToSigma :: Either a b -> Sigma (Two a b)
eitherToSigma = \case
    Left  a -> Sigma A a
    Right b -> Sigma B b

-- | Decode 'Either' from a generalised sum type.
sigmaToEither :: Sigma (Two a b) -> Either a b
sigmaToEither = \case
    Sigma A a -> Left  a
    Sigma B b -> Right b

-- | A potentially uncountable collection of tags for the same unit @()@ payload.
data Many a b where
    Many :: a -> Many a ()

many :: a -> Sigma (Many a)
many a = Sigma (Many a) ()

-- | Generalised pattern matching on a Sigma type using a Pi type to describe
-- how to handle each case.
matchPure :: Sigma t -> (forall x. t x -> x -> a) -> a
matchPure (Sigma t x) pi = pi t x

-- | A type class that allows lifting 'matchPure' into an effect 'f'.
class Functor f => Match t f | f -> t where
    pure  :: a -> f a
    match :: f (Sigma t) -> (forall x. t x -> f (x -> a)) -> f a

apply :: (t ~ One a, Match t f) => f (a -> b) -> f a -> f b
apply f x = match (Sigma One <$> x) (\One -> f)

select :: (t ~ Two a b, Match t f) => f (Either a b) -> f (a -> b) -> f b
select x f = match (eitherToSigma <$> x) $ \case
    A -> f
    B -> pure id

bind :: (t ~ Many a, Match t f) => f a -> (a -> f b) -> f b
bind x f = match (many <$> x) (\(Many x) -> const <$> f x)
