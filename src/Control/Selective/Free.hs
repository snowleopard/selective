{-# LANGUAGE FlexibleInstances, GADTs, RankNTypes, TupleSections #-}
module Control.Selective.Free (
    -- * Re-exports
    module Control.Selective,

    -- * Free functors
    Select (..), analyse, getPure, liftSelect, runSelect, foldSelect,
    getEffects, getNecessaryEffect
    ) where

import Control.Monad.Trans.Except
import Data.Bifunctor
import Data.Functor
import Data.Functor.Const
import Data.List.NonEmpty
import Control.Selective

-- Inspired by free applicative functors by Capriotti and Kaposi.
-- See: https://arxiv.org/pdf/1403.0749.pdf
-- TODO: This implementation is slow, but we could optimise it similarly to
-- http://hackage.haskell.org/package/free/docs/Control-Applicative-Free-Fast.html
-- | Free selective functors.
data Select f a where
    Pure   :: a -> Select f a
    Select :: Select f (Either a b) -> f (a -> b) -> Select f b

-- TODO: Verify that this is a lawful 'Functor'.
instance Functor f => Functor (Select f) where
    fmap k (Pure a)     = Pure (k a)
    fmap k (Select x f) = Select (fmap k <$> x) (fmap k <$>  f)

-- TODO: Verify that this is a lawful 'Applicative'.
instance Functor f => Applicative (Select f) where
    pure  = Pure
    (<*>) = apS

-- TODO: Verify that this is a lawful 'Applicative'.
instance Functor f => Selective (Select f) where
    -- Law P1
    select x (Pure f) = either f id <$> x

    -- Law A1
    select x (Select y z) = Select (select (f <$> x) (g <$> y)) (h <$> z)
      where
        f x = Right <$> x
        g y = \a -> bimap (,a) ($a) y
        h z = uncurry z

-- | Statically analyse a given selective computation and return a pair:
-- * The list of effects @fs@ that are statically known as /unnecessary/.
-- * Either
--   + The non-empty list of remaining effects @gs@, first of which is
--     statically guaranteed to be /necessary/; or
--   + The resulting value, in which case there are no necessary effects.
analyse :: Functor f => Select f a -> ([f ()], Either (NonEmpty (f ())) a)
analyse (Pure a)     = ([], Right a)
analyse (Select x f) = case analyse x of
    (fs, Right (Right x)) -> (void f : fs, Right x )
    (fs, Right (Left  _)) -> (fs         , Left (void f :| []))
    (fs, Left gs        ) -> (fs         , Left (void f <| gs))

-- | Lift a functor into a free selective computation.
liftSelect :: Functor f => f a -> Select f a
liftSelect f = Select (Pure (Left ())) (const <$> f)

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @Select f@ to @g@.
runSelect :: Selective g => (forall a. f a -> g a) -> Select f a -> g a
runSelect _ (Pure a)     = pure a
runSelect t (Select x f) = select (runSelect t x) (t f)

-- | Concatenate all effects of a free selective computation.
foldSelect :: Monoid m => (forall a. f a -> m) -> Select f a -> m
foldSelect f = getConst . runSelect (Const . f)

-- | Extract the resulting value if there are no necessary effects. This is
-- equivalent to @eitherToMaybe . snd . analyse@ but has no 'Functor' constraint.
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
