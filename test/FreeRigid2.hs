{-# LANGUAGE DeriveFunctor, GADTs, RankNTypes #-}
module FreeRigid2 (
    -- * Free rigid selective functors
    Select (..), liftSelect,

    -- * Static analysis
    getPure, getEffects, getNecessaryEffect, runSelect, foldSelect
    ) where

import Control.Monad.Trans.Except
import Control.Selective
import Data.Bifunctor
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
    fmap f (Select x y) = Select (bimap (f.) f <$> x) y

-- TODO: Prove that this is a lawful 'Applicative'.
instance Functor f => Applicative (Select f) where
    pure  = Pure
    (<*>) = apS -- Rigid selective functors

-- TODO: Prove that this is a lawful 'Selective'.
instance Functor f => Selective (Select f) where
    select = selectBy (first (flip ($)))
      where
        selectBy :: (a -> Either (b -> c) c) -> Select f a -> Select f b -> Select f c
        selectBy f x (Pure y)     = either ($y) id . f <$> x
        selectBy f x (Select y z) = Select (selectBy h x y) z -- O(N)
          where
            h a = case f a of Right r -> Right (Right r)
                              Left dr -> Left  (bimap (dr.) dr)

-- | Lift a functor into a free selective computation.
liftSelect :: f a -> Select f a
liftSelect f = Select (Pure (Left id)) f

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @Select f@ to @g@.
runSelect :: Selective g => (forall x. f x -> g x) -> Select f a -> g a
runSelect _ (Pure a)     = pure a
runSelect t (Select x y) = select (runSelect t x) (flip ($) <$> t y)

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
