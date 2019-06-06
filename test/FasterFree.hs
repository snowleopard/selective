{-# LANGUAGE DeriveFunctor, GADTs, RankNTypes #-}
module FasterFree (
    -- * Free rigid selective functors
    Select (..), liftSelect,

    -- * Static analysis
    getPure, getEffects, getNecessaryEffect, runSelect, foldSelect
    ) where

import Control.Monad.Trans.Except
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

----------------------------- Alternative Selective ----------------------------
class Applicative f => Selective f where
    select :: (a -> Either (b -> c) c) -> f a -> f b -> f c

newtype Over m a = Over { getOver :: m }
    deriving (Eq, Functor, Ord, Show)

instance Monoid m => Applicative (Over m) where
    pure _            = Over mempty
    Over x <*> Over y = Over (mappend x y)

instance Monoid m => Selective (Over m) where
    select _ (Over x) (Over y) = Over (mappend x y)

instance            Selective Maybe         where select = selectM
instance Monad m => Selective (ExceptT e m) where select = selectM

apS :: Selective f => f (a -> b) -> f a -> f b
apS = select Left

selectM :: Monad f => (a -> Either (b -> c) c) -> f a -> f b -> f c
selectM f x y = x >>= \a -> case f a of Left bc -> bc <$> y -- execute y
                                        Right c -> pure c   -- skip y


--------------------------- Faster free construction ---------------------------

-- | Free rigid selective functors.
data Select f a where
    Pure   :: a -> Select f a
    Select :: (a -> Either (b -> c) c) -> Select f a -> f b -> Select f c

-- TODO: Prove that this is a lawful 'Functor'.
instance Functor (Select f) where
    fmap f (Pure a)       = Pure (f a)
    fmap f (Select g x y) = Select (bimap (f.) f <$> g) x y -- No fmap!

-- TODO: Prove that this is a lawful 'Applicative'.
instance Functor f => Applicative (Select f) where
    pure  = Pure
    (<*>) = apS -- Rigid selective functors

-- TODO: Prove that this is a lawful 'Selective'.
instance Functor f => Selective (Select f) where
    -- Identity law
    select f x (Pure y) = either ($y) id . f <$> x

    -- Associativity law
    select f x (Select g y z) = Select id (select h x y) z
      where
        h a = case f a of Right r -> Right (Right r)
                          Left dr -> Left  (bimap (dr.) dr . g)

-- | Lift a functor into a free selective computation.
liftSelect :: f a -> Select f a
liftSelect f = Select (const $ Left id) (Pure ()) f

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @Select f@ to @g@.
runSelect :: Selective g => (forall x. f x -> g x) -> Select f a -> g a
runSelect _ (Pure a)       = pure a
runSelect t (Select f x y) = select f (runSelect t x) (t y)

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
