{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Selective.Free
-- Copyright  : (c) Andrey Mokhov 2018-2023
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- This is a library for /selective applicative functors/, or just
-- /selective functors/ for short, an abstraction between applicative functors
-- and monads, introduced in this paper:
-- https://www.staff.ncl.ac.uk/andrey.mokhov/selective-functors.pdf.
--
-- This module defines /free selective functors/ using the ideas from the
-- Sjoerd Visscher's package 'free-functors':
-- https://hackage.haskell.org/package/free-functors-1.0.1/docs/Data-Functor-HFree.html.
--
-----------------------------------------------------------------------------
module Control.Selective.Free (
    -- * Free selective functors
    Select (..), liftSelect,

    -- * Static analysis
    getPure, getEffects, getNecessaryEffects, runSelect, foldSelect
    ) where

import Control.Selective
import Data.Functor

-- | Free selective functors.
newtype Select f a = Select (forall g. Selective g => (forall x. f x -> g x) -> g a)

-- Ignoring the hint, since GHC can't type check the suggested code.
{-# ANN module "HLint: ignore Use fmap" #-}
instance Functor (Select f) where
    fmap f (Select x) = Select $ \k -> f <$> x k

instance Applicative (Select f) where
    pure a                = Select $ \_ -> pure a
    Select x <*> Select y = Select $ \k -> x k <*> y k

instance Selective (Select f) where
    select (Select x) (Select y) = Select $ \k -> x k <*? y k

-- | Lift a functor into a free selective computation.
liftSelect :: f a -> Select f a
liftSelect x = Select (\f -> f x)

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @Select f@ to @g@. Note that here we rely on the
-- fact that @g@ is a lawful selective functor.
runSelect :: Selective g => (forall x. f x -> g x) -> Select f a -> g a
runSelect k (Select x) = x k

-- | Concatenate all effects of a free selective computation.
foldSelect :: Monoid m => (forall x. f x -> m) -> Select f a -> m
foldSelect f = getOver . runSelect (Over . f)

-- | Extract the resulting value if there are no necessary effects.
getPure :: Select f a -> Maybe a
getPure = runSelect (const Nothing)

-- | Collect /all possible effects/ in the order they appear in a free selective
-- computation.
getEffects :: Functor f => Select f a -> [f ()]
getEffects = foldSelect (pure . void)

-- | Extract /all necessary effects/ in the order they appear in a free
-- selective computation.
getNecessaryEffects :: Functor f => Select f a -> [f ()]
getNecessaryEffects = getUnder . runSelect (Under . pure . void)
