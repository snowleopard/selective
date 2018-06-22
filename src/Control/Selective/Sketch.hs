{-# LANGUAGE TupleSections, ScopedTypeVariables #-}
module Control.Selective.Sketch where

import Control.Selective
import Data.Bifunctor
import Data.Void

-- Associate to the left
-- f (a + b + c) -> f (a -> (b + c)) -> f (b -> c) -> f c
l :: Selective f => f (Either a (Either b c)) -> f (a -> Either b c) -> f (b -> c) -> f c
l x y z = x <*? y <*? z

-- Associate to the right
-- f (a + b) -> f (c + (a -> b)) -> f (c -> a -> b) -> f b
r :: Selective f => f (Either a b) -> f (Either c (a -> b)) -> f (c -> a -> b) -> f b
r x y z = x <*? (y <*? z)

-- Normalise: go from right to left association
k :: Selective f => f (Either a b) -> f (Either c (a -> b)) -> f (c -> a -> b) -> f b
k x y z = fmap Right <$> x <*? ((\x a -> bimap (,a) ($a) x) <$> y) <*? (uncurry <$> z)

-- Alternative definition, we could also add @pureS :: f (a -> a)@
-- * The first effect must be evaluated.
-- * Associativity: x .? (y .? z) == (x .? y) .? z
-- * (f .) <$> x .? y   == (f .) <$> (x .? y)
-- * x .? ((. f) <$> y) == (. f) <$> (x .? y)
class Applicative f => Selective2 f where
    (.?) :: f (Either e (b -> c)) -> f (Either e (a -> b)) -> f (Either e (a -> c))

infixl 4 .?

-- Another alternative definition, analogous to Applicative
-- * The first effect must be evaluated.
class Applicative f => Selective3 f where
    (*?) :: f (Either e (a -> b)) -> f (Either e a) -> f (Either e b)

infixl 4 *?

-- Proving equivalence: go from Selective2 to Selective
from2 :: Selective2 f => f (Either a b) -> f (a -> b) -> f b
from2 x f = either id ($()) <$> (Right <$> f .? (fmap const . mirror <$> x))

-- Proving equivalence: go from Selective to Selective2
to2 :: Selective f => f (Either e (b -> c)) -> f (Either e (a -> b)) -> f (Either e (a -> c))
to2 f g = mirror <$> handle (fmap Right . mirror <$> f) ((\x bc -> first (bc.) $ mirror x) <$> g)

mirror :: Either a b -> Either b a
mirror (Left  x) = Right x
mirror (Right x) = Left  x

-- x .* (y .* z) == (x .* y) .* z
--
--         <===>
--
-- (Right <$> x .? (Right <$> (either absurd id <$> (Right <$> y .? (Right <$> z)))))
--    ==
-- (Right <$> (either absurd id <$> (Right <$> x .? (Right <$> y))) .? (Right <$> z))
(.*) :: Selective2 f => f (b -> c) -> f (a -> b) -> f (a -> c)
f .* g = either absurd id <$> (Right <$> f .? (Right <$> g))

-- handle (pure (Left x)) f        == fmap ($x) f
-- handle x               (pure f) == fmap (bimap f id) x

-- f <$> handle x y            == handle (bimap id f <$> x) ((f .) <$> y)
-- handle (bimap f id <$> x) y == handle x                  ((. f) <$> y)
