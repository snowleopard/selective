{-# LANGUAGE GADTs, RankNTypes, TupleSections #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Selective.Rigid.Free
-- Copyright  : (c) Andrey Mokhov 2018-2024
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- This is a library for /selective applicative functors/, or just
-- /selective functors/ for short, an abstraction between applicative functors
-- and monads, introduced in this paper: https://dl.acm.org/doi/10.1145/3341694.
--
-- This module defines /free rigid selective functors/. Rigid selective functors
-- are those that satisfy the property @\<*\> = apS@.
--
-- Intuitively, a selective functor @f@ is "rigid" if any expression @f a@ is
-- equivalent to a list of effects chained with @select@ operators (the normal
-- form given by the free construction). In contrast, "non-rigid" selective
-- functors can have non-linear, tree-like shapes, because @<*>@ nodes can't be
-- straightened using the @\<*\> = apS@ equation.
--
-----------------------------------------------------------------------------
module Control.Selective.Rigid.Free (
    -- * Free rigid selective functors
    Select (..), liftSelect,

    -- * Static analysis
    getPure, getEffects, getNecessaryEffect, runSelect, foldSelect
    ) where

import Control.Selective.Trans.Except
import Control.Selective
import Data.Bifunctor
import Data.Functor

-- Inspired by free applicative functors by Capriotti and Kaposi.
-- See: https://arxiv.org/pdf/1403.0749.pdf

-- TODO: The current approach is simple but very slow: 'fmap' costs O(N), where
-- N is the number of effects, and 'select' is even worse -- O(N^2). It is
-- possible to improve both bounds to O(1) by using the idea developed for free
-- applicative functors by Dave Menendez. See this blog post:
-- https://www.eyrie.org/~zednenem/2013/05/27/freeapp
-- An example implementation can be found here:
-- http://hackage.haskell.org/package/free/docs/Control-Applicative-Free-Fast.html

-- | Free rigid selective functors.
data Select f a where
    Pure   :: a -> Select f a
    Select :: Select f (Either a b) -> f (a -> b) -> Select f b

-- TODO: Prove that this is a lawful 'Functor'.
instance Functor f => Functor (Select f) where
    fmap f (Pure a)     = Pure (f a)
    fmap f (Select x y) = Select (fmap f <$> x) (fmap f <$> y)

-- TODO: Prove that this is a lawful 'Applicative'.
instance Functor f => Applicative (Select f) where
    pure  = Pure
    (<*>) = apS -- Rigid selective functors

-- TODO: Prove that this is a lawful 'Selective'.
instance Functor f => Selective (Select f) where
    -- Identity law
    select x (Pure y) = either y id <$> x

    -- Associativity law
    select x (Select y z) = Select (select (f <$> x) (g <$> y)) (h <$> z)
      where
        f     = fmap Right
        g y a = bimap (,a) ($a) y
        h     = uncurry

{- The following can be used in the above implementation as select = selectOpt.

-- An optimised implementation of select for the free instance. It accumulates
-- the calls to fmap on the @y@ parameter to avoid traversing the list on every
-- recursive step.
selectOpt :: Functor f => Select f (Either a b) -> Select f (a -> b) -> Select f b
selectOpt x y = go x y id

-- We turn @Select f (a -> b)@ to @(Select f c, c -> (a -> b))@. Hey, co-Yoneda!
go :: Functor f => Select f (Either a b) -> Select f c -> (c -> (a -> b)) -> Select f b
go x (Pure y)     k = either (k y) id <$> x
go x (Select y z) k = Select (go (f <$> x) y (g . second k)) ((h . (k.)) <$> z)
  where
    f x = Right <$> x
    g y = \a -> bimap (,a) ($a) y
    h z = uncurry z
-}

-- | Lift a functor into a free selective computation.
liftSelect :: Functor f => f a -> Select f a
liftSelect f = Select (Pure (Left ())) (const <$> f)

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @Select f@ to @g@.
runSelect :: Selective g => (forall x. f x -> g x) -> Select f a -> g a
runSelect _ (Pure a)     = pure a
runSelect t (Select x y) = select (runSelect t x) (t y)

-- | Concatenate all effects of a free selective computation.
foldSelect :: Monoid m => (forall x. f x -> m) -> Select f a -> m
foldSelect f = getOver . runSelect (Over . f)

-- | Extract the resulting value if there are no necessary effects.
getPure :: Select f a -> Maybe a
getPure = runSelect (const Nothing)

-- | Collect all possible effects in the order they appear in a free selective
-- computation.
getEffects :: Functor f => Select f a -> [f ()]
getEffects = foldSelect (pure . void)

-- Implementation used in the paper:
-- getEffects = getOver . runSelect (Over . pure . void)

-- | Extract the necessary effect from a free selective computation. Note: there
-- can be at most one effect that is statically guaranteed to be necessary.
getNecessaryEffect :: Functor f => Select f a -> Maybe (f ())
getNecessaryEffect = leftToMaybe . runExcept . runSelect (throwE . void)

leftToMaybe :: Either a b -> Maybe a
leftToMaybe (Left a) = Just a
leftToMaybe _        = Nothing
