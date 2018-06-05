{-# LANGUAGE GADTs, RankNTypes, TupleSections #-}
module Control.Selective.Free (
    -- * Free selective functors
    Select (..), runSelect
    ) where

import Data.Bifunctor

-- Inspired by free applicative functors by Capriotti and Kaposi
-- Beware of bugs in this code; I have only compiled it, not proved it correct.
data Select f a where
    Pure   :: a -> Select f a
    Handle :: Select f (a -> b) -> f (Either a b) -> Select f b

instance Functor f => Functor (Select f) where
    fmap f (Pure x)     = Pure (f x)
    fmap f (Handle g x) = Handle (fmap (fmap f) g) (fmap (fmap f) x)

instance Functor f => Applicative (Select f) where
    pure  = Pure
    (<*>) = apS

liftSelect :: Functor f => f a -> Select f a
liftSelect fa = Handle (Pure id) (fmap Left fa)

instance Functor f => Selective (Select f) where
    handle (Pure f) x     = fmap (either f id) x
    handle (Handle f x) y = handle (fmap uncurry f) $ handle
        (liftSelect $ fmap (\x a -> bimap (,a) ($a) x) x) (fmap (fmap Right) y)

runSelect :: Selective g => (forall a. f a -> g a) -> Select f a -> g a
runSelect _ (Pure a)     = pure a
runSelect t (Handle f x) = handle (runSelect t f) (t x)
