{-# LANGUAGE GADTs, RankNTypes, TupleSections #-}
module Control.Selective.Free (
    -- * Free selective functors
    Select (..), runSelect
    ) where

import Data.Bifunctor
import Control.Selective

-- Inspired by free applicative functors by Capriotti and Kaposi.
-- Beware of bugs in this code; I have only compiled it, not proved it correct.
data Select f a where
    Pure   :: a -> Select f a
    Handle :: f (Either a b) -> Select f (a -> b) -> Select f b

instance Functor f => Functor (Select f) where
    fmap f (Pure x)     = Pure (f x)
    fmap f (Handle x y) = Handle (second f <$> x) ((f .) <$> y) -- Law F1

instance Functor f => Applicative (Select f) where
    pure  = Pure
    (<*>) = apS

liftSelect :: Functor f => f a -> Select f a
liftSelect fa = Handle (Left <$> fa) (Pure id) -- Law P1

instance Functor f => Selective (Select f) where
    handle x (Pure y)     = either y id <$> x -- Law P1
    handle x (Handle y z) = handle -- Law A1
        (handle (fmap Right <$> x) (liftSelect $ (\k a -> bimap (,a) ($a) k) <$> y))
        (uncurry <$> z)

runSelect :: Selective g => (forall a. f a -> g a) -> Select f a -> g a
runSelect _ (Pure a)     = pure a
runSelect t (Handle x f) = handle (t x) (runSelect t f)
