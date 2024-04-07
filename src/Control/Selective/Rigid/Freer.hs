{-# LANGUAGE DeriveFunctor, GADTs, RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Selective.Rigid.Freer
-- Copyright  : (c) Andrey Mokhov 2018-2024
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- This is a library for /selective applicative functors/, or just
-- /selective functors/ for short, an abstraction between applicative functors
-- and monads, introduced in this paper: https://dl.acm.org/doi/10.1145/3341694.
--
-- This module defines /freer rigid selective functors/. Rigid selective
-- functors are those that satisfy the property @\<*\> = apS@. Compared to the
-- "free" construction from "Control.Selective.Rigid.Free", this "freer"
-- construction does not require the underlying base data type to be a functor.
--
-----------------------------------------------------------------------------
module Control.Selective.Rigid.Freer (
    -- * Free rigid selective functors
    Select (..), liftSelect,

    -- * Static analysis
    getPure, getEffects, getNecessaryEffect, runSelect, foldSelect
    ) where

import Control.Selective.Trans.Except
import Control.Selective
import Data.Bifunctor
import Data.Function
import Data.Functor

-- Inspired by free applicative functors by Capriotti and Kaposi.
-- See: https://arxiv.org/pdf/1403.0749.pdf

-- Note: In the current implementation, 'fmap' and 'select' cost O(N), where N
-- is the number of effects. It is possible to improve this to O(1) by using the
-- idea developed for free applicative functors by Dave Menendez, see this blog
-- post: https://www.eyrie.org/~zednenem/2013/05/27/freeapp.
-- An example implementation can be found here:
-- http://hackage.haskell.org/package/free/docs/Control-Applicative-Free-Fast.html

-- | Free rigid selective functors.
data Select f a where
    Pure   :: a -> Select f a
    Select :: Select f (Either (x -> a) a) -> f x -> Select f a

-- TODO: Prove that this is a lawful 'Functor'.
instance Functor (Select f) where
    fmap f (Pure a)     = Pure (f a)
    fmap f (Select x y) = Select (bimap (f.) f <$> x) y -- O(N)

-- TODO: Prove that this is a lawful 'Applicative'.
instance Applicative (Select f) where
    pure  = Pure
    (<*>) = apS -- Rigid selective functors

-- TODO: Prove that this is a lawful 'Selective'.
instance Selective (Select f) where
    select = selectBy (first (&))
      where
        selectBy :: (a -> Either (b -> c) c) -> Select f a -> Select f b -> Select f c
        selectBy f x (Pure y)     = either ($y) id . f <$> x
        selectBy f x (Select y z) = Select (selectBy g x y) z -- O(N)
          where
            g a = case f a of Right c -> Right (Right c)
                              Left bc -> Left  (bimap (bc.) bc)

-- | Lift a functor into a free selective computation.
liftSelect :: f a -> Select f a
liftSelect = Select (Pure (Left id))

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @Select f@ to @g@.
runSelect :: Selective g => (forall x. f x -> g x) -> Select f a -> g a
runSelect _ (Pure a)     = pure a
runSelect t (Select x y) = select (runSelect t x) ((&) <$> t y)

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

-- | Extract the necessary effect from a free selective computation. Note: there
-- can be at most one effect that is statically guaranteed to be necessary.
getNecessaryEffect :: Functor f => Select f a -> Maybe (f ())
getNecessaryEffect = leftToMaybe . runExcept . runSelect (throwE . void)

leftToMaybe :: Either a b -> Maybe a
leftToMaybe (Left a) = Just a
leftToMaybe _        = Nothing
