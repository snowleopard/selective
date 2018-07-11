{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections #-}
module Control.Selective.Free (
    -- * Re-exports
    module Control.Selective,

    -- * Free selective functors
    Select (..), liftSelect, getPure, unnecessaryEffects, necessaryEffect,
    allEffects, runSelect
    ) where

import Data.Bifunctor
import Data.Functor
import Data.Void
import Control.Selective

-- Inspired by free applicative functors by Capriotti and Kaposi.
-- Beware of bugs in this code; I have only compiled it, not proved it correct.
-- Invariant: the 'Select' tree terminates with a @Pure (Left x)@, i.e. all
-- occurrences of @Pure (Right x)@ have been turned into unnecessary @Effect@s.
data Select f a where
    Pure   :: a -> Select f a
    Effect :: Select f a -> f () -> Select f a
    Handle :: Select f (Either a b) -> f (a -> b) -> Select f b

-- | Determine the result of a computation statically.
getPure :: Select f a -> Maybe a
getPure (Pure x)     = Just x
getPure (Effect x _) = getPure x -- Skip an unnecessary effect
getPure (Handle _ _) = Nothing   -- There is a necessary effect

-- | The list of effects which are statically known as unnecessary.
unnecessaryEffects :: Select f a -> [f ()]
unnecessaryEffects (Pure   _  ) = []
unnecessaryEffects (Effect x f) = unnecessaryEffects x ++ [f]
unnecessaryEffects (Handle x _) = unnecessaryEffects x -- f may be necessary

-- | The only effect which is statically known as necessary. Returns @Nothing@
-- if the computation is pure.
necessaryEffect :: Functor f => Select f a -> Maybe (f ())
necessaryEffect (Effect x _)               = necessaryEffect x
necessaryEffect (Handle (Pure (Left _)) f) = Just (void f)
necessaryEffect (Handle x               _) = necessaryEffect x
necessaryEffect _                          = Nothing

-- | The list of all effects that appear in the computation.
allEffects :: Functor f => Select f a -> [f ()]
allEffects (Pure _)     = []
allEffects (Effect x f) = allEffects x ++ [f]
allEffects (Handle x f) = allEffects x ++ [void f]

-- TODO: The current implementation is slow, but we could optimise it similarly to
-- http://hackage.haskell.org/package/free/docs/Control-Applicative-Free-Fast.html
instance Functor f => Functor (Select f) where
    fmap f (Pure   x  ) = Pure (f x)
    fmap f (Effect x y) = Effect (fmap f x) y
    fmap f (Handle x y) = Handle (second f <$> x) ((f .) <$> y) -- Law F1

instance Functor f => Applicative (Select f) where
    pure  = Pure
    (<*>) = apS

-- | Lift a functor into a free selective computation.
liftSelect :: Functor f => f a -> Select f a
liftSelect f = Handle (Pure (Left ())) (const <$> f) -- Law P1

-- TODO: Optimise
instance Functor f => Selective (Select f) where
    handle x                (Pure y)     = either y id <$> x -- Law P1
    handle x                (Effect y f) = Effect (handle x y) f
    handle (Pure (Left  x)) y            = ($x) <$> y -- Law P2
    handle (Pure (Right x)) y            = foldr (flip Effect) (Pure x) (allEffects y)
    handle x                (Handle y f) = Handle -- Law A1
        (handle (fmap Right <$> x) ((\k a -> bimap (,a) ($a) k) <$> y))
        (uncurry <$> f)

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @Select f@ to @g@.
runSelect :: Selective g => (forall a. f a -> g a) -> Select f a -> g a
runSelect _ (Pure a)     = pure a
runSelect t (Effect x f) = handle (Right <$> runSelect t x) (const absurd <$> t f)
runSelect t (Handle x f) = handle (runSelect t x) (t f)
