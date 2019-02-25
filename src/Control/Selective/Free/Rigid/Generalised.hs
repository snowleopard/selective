-- Free selective functors for the simple case when @<*> = apS@.
-- This module uses a generalised approach to constructing free structures.
-- See "Control.Selective.Free" for a simpler, non-generalised approach.
{-# LANGUAGE FlexibleInstances, GADTs, KindSignatures, RankNTypes #-}
{-# LANGUAGE TupleSections, TypeOperators #-}
module Control.Selective.Free.Rigid.Generalised (
    -- * Re-exports
    module Control.Selective,

    -- * Free functors
    FreeA, FreeS, FreeM, analyse, liftS, runS
    ) where

import Data.Bifunctor
import Data.Functor
import Data.List.NonEmpty
import Control.Selective

-- This is a generalised free construction that works for free applicative and
-- selective functors, as well as monads. See "Control.Selective.Free" for a
-- non-generalised version.

-- Three ways of composing functors, whose definitions mirror the type
-- signatures of the Applicative's (<*>), Selective's (<*?>) and Monad's (>>=)
-- operators.
-- Inspired by these awesome blog posts by Bartosz Milewski and Oleg Grenrus:
-- https://bartoszmilewski.com/2018/02/17/free-monoidal-functors/
-- http://oleg.fi/gists/posts/2018-02-21-single-free.html
data (:+:) f g a where
    (:+:) :: f x -> g (x -> a) -> (f :+: g) a

data (:|:) f g a where
    (:|:) :: f (x -> a) -> g (Either x a) -> (:|:) f g a

data (:*:) f g a where
    (:*:) :: f x -> (x -> g a) -> (:*:) f g a

data Free (p :: (* -> *) -> (* -> *) -> (* -> *)) f a
    = Done a
    | More (p f (Free p f) a)

type FreeA = Free (:+:)
type FreeS = Free (:|:)
type FreeM = Free (:*:)

instance Functor g => Functor (f :+: g) where
    fmap k (f :+: g) = f :+: fmap (fmap k) g

instance (Functor f, Functor g) => Functor (f :|: g) where
    fmap k (f :|: g) = fmap (fmap k) f :|: fmap (fmap k) g

instance Functor g => Functor (f :*: g) where
    fmap k (f :*: g) = f :*: fmap (fmap k) g

instance Functor f => Functor (Free (:|:) f) where
    fmap k (Done a) = Done (k a)
    fmap k (More f) = More (fmap k f)

instance Functor f => Applicative (Free (:|:) f) where
    pure  = Done
    (<*>) = apS

-- Inspired by free applicative functors by Capriotti and Kaposi.
-- TODO: This implementation is slow, but we could optimise it similarly to
-- http://hackage.haskell.org/package/free/docs/Control-Applicative-Free-Fast.html
instance Functor f => Selective (FreeS f) where
    -- Law P1
    select x (Done f) = either f id <$> x

    -- Law A1
    select x (More (z :|: y)) = More ((h <$> z) :|: select (f <$> x) (g <$> y))
      where
        f x = Right <$> x
        g y = \a -> bimap (,a) ($a) y
        h z = uncurry z

-- | Statically analyse a given selective computation and return a pair (fs, x)
-- comprising:
-- * The list of effects @fs@ that are statically known as unnecessary.
-- * Either
--   - The non-empty list of remaining effects @gs@, first of which is
--     statically known to be necessary; or
--   - The resulting value, in which case there are no necessary effects.
analyse :: Functor f => FreeS f a -> ([f ()], Either (NonEmpty (f ())) a)
analyse (Done a)         = ([], Right a)
analyse (More (f :|: x)) = case analyse x of
    (fs, Right (Right x)) -> (void f : fs, Right x )
    (fs, Right (Left  _)) -> (fs         , Left (void f :| []))
    (fs, Left gs        ) -> (fs         , Left (void f <| gs))

-- | Lift a functor into a free selective computation.
liftS :: Functor f => f a -> FreeS f a
liftS f = More $ fmap const f :|: Done (Left ())

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @FreeS f@ to @g@.
runS :: Selective g => (forall a. f a -> g a) -> FreeS f a -> g a
runS _ (Done a)         = pure a
runS t (More (f :|: x)) = select (runS t x) (t f)
