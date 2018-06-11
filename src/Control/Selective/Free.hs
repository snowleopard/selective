{-# LANGUAGE GADTs, RankNTypes, TupleSections #-}
module Control.Selective.Free (
    -- * Free selective functors
    Select (..), runSelect
    ) where

import Data.Bifunctor
import Control.Selective

-- Inspired by free applicative functors by Capriotti and Kaposi
-- Beware of bugs in this code; I have only compiled it, not proved it correct.
data Select f a where
    Pure   :: a -> Select f a
    Handle :: f (Either a b) -> Select f (a -> b) -> Select f b

instance Functor f => Functor (Select f) where
    fmap f (Pure x)     = Pure (f x)
    fmap f (Handle x g) = Handle (fmap (fmap f) x) (fmap (fmap f) g)

instance Functor f => Applicative (Select f) where
    pure  = Pure
    (<*>) = apS

liftSelect :: Functor f => f a -> Select f a
liftSelect fa = Handle (fmap Left fa) (Pure id)

instance Functor f => Selective (Select f) where
    handle x (Pure f)     = fmap (either f id) x
    handle x (Handle y f) = handle
        (handle (fmap (fmap Right) x) (liftSelect $ fmap (\x a -> bimap (,a) ($a) x) y))
        (fmap uncurry f)

runSelect :: Selective g => (forall a. f a -> g a) -> Select f a -> g a
runSelect _ (Pure a)     = pure a
runSelect t (Handle x f) = handle (t x) (runSelect t f)
