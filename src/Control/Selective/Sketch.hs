{-# LANGUAGE TupleSections, ScopedTypeVariables #-}
module Control.Selective.Sketch where

import Control.Selective
import Data.Bifunctor
import Data.Void

-------------------------------- Proof sketches --------------------------------

-- A convenient primitive checking that the types of two given values coincide
-- and returns the first value.
(===) :: a -> a -> a
x === y = if True then x else y

infixl 0 ===

-- First, we typecheck the laws

-- F1: f <$> handle x y = handle (second f <$> x) ((f .) <$> y)
f1 :: Selective f => (b -> c) -> f (Either a b) -> f (a -> b) -> f c
f1 f x y = f <$> handle x y === handle (second f <$> x) ((f .) <$> y)

-- F2: handle (first f <$> x) y = handle x ((. f) <$> y)
f2 :: Selective f => (a -> c) -> f (Either a b) -> f (c -> b) -> f b
f2 f x y = handle (first f <$> x) y === handle x ((. f) <$> y)

-- F3: handle x (f <$> y) = handle (first (flip f) <$> x) (flip ($) <$> y)
f3 :: Selective f => (c -> a -> b) -> f (Either a b) -> f c -> f b
f3 f x y = handle x (f <$> y) === handle (first (flip f) <$> x) (flip ($) <$> y)

-- P1: handle x (pure y) == either y id <$> x
p1 :: Selective f => f (Either a b) -> (a -> b) -> f b
p1 x y = handle x (pure y) === either y id <$> x

-- P2: handle (pure (Left x)) y = ($x) <$> y
p2 :: Selective f => a -> f (a -> b) -> f b
p2 x y = handle (pure (Left x)) y === ($x) <$> y

-- A1: handle x (handle y z) = handle (handle (f <$> x) (g <$> y)) (h <$> z)
--       where f x = Right <$> x
--             g y = \a -> bimap (,a) ($a) y
--             h z = uncurry z
a1 :: Selective f => f (Either a b) -> f (Either c (a -> b)) -> f (c -> a -> b) -> f b
a1 x y z = handle x (handle y z) === handle (handle (f <$> x) (g <$> y)) (h <$> z)
  where
    f x = Right <$> x
    g y = \a -> bimap (,a) ($a) y
    h z = uncurry z

-- Now let's typecheck some theorems

-- Identity: pure id <*> v = v
t1 :: Selective f => f a -> f a
t1 v =
    -- Express the lefthand side using 'apS'
    apS (pure id) v
    === -- Definition of 'apS'
    handle (Left <$> pure id) (flip ($) <$> v)
    === -- Push 'Left' inside 'pure'
    handle (pure (Left id)) (flip ($) <$> v)
    === -- Apply P2
    ($id) <$> (flip ($) <$> v)
    === -- Simplify
    id <$> v
    === -- Functor identity: fmap id = id
    v

-- Homomorphism: pure f <*> pure x = pure (f x)
t2 :: Selective f => (a -> b) -> a -> f b
t2 f x =
    -- Express the lefthand side using 'apS'
    apS (pure f) (pure x)
    === -- Definition of 'apS'
    handle (Left <$> pure f) (flip ($) <$> pure x)
    === -- Push 'Left' inside 'pure'
    handle (pure (Left f)) (flip ($) <$> pure x)
    === -- Apply P2
    ($f) <$> (flip ($) <$> pure x)
    === -- Simplify
    f <$> pure x
    === -- Apply a pure function to a pure value (pure f <*> pure x)
    pure (f x)

-- Interchange: u <*> pure y = pure ($y) <*> u
t3 :: Selective f => f (a -> b) -> a -> f b
t3 u y =
    -- Express the lefthand side using 'apS'
    apS u (pure y)
    === -- Definition of 'apS'
    handle (Left <$> u) (flip ($) <$> pure y)
    === -- Rewrite to have a pure handler
    handle (Left <$> u) (pure ($y))
    === -- Apply P1
    either ($y) id <$> (Left <$> u)
    === -- Simplify, obtaining (#)
    ($y) <$> u

    === -- Express right-hand side of the theorem using 'apS'
    apS (pure ($y)) u
    === -- Definition of 'apS'
    handle (Left <$> pure ($y)) (flip ($) <$> u)
    === -- Push 'Left' inside 'pure'
    handle (pure (Left ($y))) (flip ($) <$> u)
    === -- Apply P2
    ($($y)) <$> (flip ($) <$> u)
    === -- Simplify, obtaining (#)
    ($y) <$> u

-- Composition: (.) <$> u <*> v <*> w = u <*> (v <*> w)
t4 :: Selective f => f (b -> c) -> f (a -> b) -> f a -> f c
t4 u v w =
    -- Express the lefthand side using 'apS'
    apS (apS ((.) <$> u) v) w
    === -- Definition of 'apS'
    handle (Left <$> handle (Left <$> (.) <$> u) (flip ($) <$> v)) (flip ($) <$> w)
    === -- Apply F1 to push the leftmost 'Left' inside 'handle'
    handle (handle (second Left <$> Left <$> (.) <$> u) ((Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    === -- Simplify
    handle (handle (Left <$> (.) <$> u) ((Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    === -- Pull (.) outside 'Left'
    handle (handle (first (.) <$> Left <$> u) ((Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    === -- Apply F2 to push @(.)@ to the handler
    handle (handle (Left <$> u) ((. (.)) <$> (Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    === -- Simplify, obtaining (#)
    handle (handle (Left <$> u) ((Left .) <$> flip (.) <$> v)) (flip ($) <$> w)

    === -- Express the righthand side using 'apS'
    apS u (apS v w)
    === -- Definition of 'apS'
    handle (Left <$> u) (flip ($) <$> handle (Left <$> v) (flip ($) <$> w))
    === -- Apply F1 to push @flip ($)@ inside 'handle'
    handle (Left <$> u) (handle (Left <$> v) ((flip ($) .) <$> flip ($) <$> w))
    === -- Apply A1 to reassociate to the left
    handle (handle (Left <$> u) ((\y a -> bimap (,a) ($a) y) <$> Left <$> v)) (uncurry . (flip ($) .) <$> flip ($) <$> w)
    === -- Simplify
    handle (handle (Left <$> u) ((\y a -> Left (y, a)) <$> v)) ((\x (f, g) -> g (f x)) <$> w)
    === -- Apply F3 to pull the rightmost pure function inside 'handle'
    handle (first (flip ((\x (f, g) -> g (f x)))) <$> handle (Left <$> u) ((\y a -> Left (y, a)) <$> v)) (flip ($) <$> w)
    === -- Simplify
    handle (first (\(f, g) -> g . f) <$> handle (Left <$> u) ((\y a -> Left (y, a)) <$> v)) (flip ($) <$> w)
    === -- Apply F1 to push the leftmost pure function inside 'handle'
    handle (handle (Left <$> u) (((first (\(f, g) -> g . f)).) <$> (\y a -> Left (y, a)) <$> v)) (flip ($) <$> w)
    === -- Simplify, obtaining (#)
    handle (handle (Left <$> u) ((Left .) <$> flip (.) <$> v)) (flip ($) <$> w)

--------------------------------- End of proofs --------------------------------

-- Various other sketches below

-- Associate to the left
-- f (a + b + c) -> f (a -> (b + c)) -> f (b -> c) -> f c
l :: Selective f => f (Either a (Either b c)) -> f (a -> Either b c) -> f (b -> c) -> f c
l x y z = x <*? y <*? z

-- Associate to the right
-- f (a + b) -> f (c + (a -> b)) -> f (c -> a -> b) -> f b
r :: Selective f => f (Either a b) -> f (Either c (a -> b)) -> f (c -> a -> b) -> f b
r x y z = x <*? (y <*? z)

-- Normalise: go from right to left association
normalise :: Selective f => f (Either a b) -> f (Either c (a -> b)) -> f (c -> a -> b) -> f b
normalise x y z = (f <$> x) <*? (g <$> y) <*? (h <$> z)
  where
    f x = Right <$> x
    g y = \a -> bimap (,a) ($a) y
    h z = uncurry z

-- Alternative normalisation which uses Scott encoding of pairs
normalise2 :: Selective f => f (Either a b) -> f (Either c (a -> b)) -> f (c -> a -> b) -> f b
normalise2 x y z = (f <$> x) <*? (g <$> y) <*? (h <$> z)
  where
    f x = Right <$> x
    g y = \a -> bimap (\c f -> f c a) ($a) y
    h z = ($z) -- h = flip ($)

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
(.*) :: Selective2 f => f (b -> c) -> f (a -> b) -> f (a -> c)
f .* g = either absurd id <$> (Right <$> f .? (Right <$> g))
