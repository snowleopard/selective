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
f1 f x y = lhs === rhs
  where
    lhs = f <$> handle x y
    rhs = handle (second f <$> x) ((f .) <$> y)

-- F2: handle (first f <$> x) y = handle x ((. f) <$> y)
f2 :: Selective f => (a -> c) -> f (Either a b) -> f (c -> b) -> f b
f2 f x y = lhs === rhs
  where
    lhs = handle (first f <$> x) y
    rhs = handle x ((. f) <$> y)

-- F3: handle x (f <$> y) = handle (first (flip f) <$> x) (flip ($) <$> y)
f3 :: Selective f => (c -> a -> b) -> f (Either a b) -> f c -> f b
f3 f x y = lhs === rhs
  where
    lhs = handle x (f <$> y)
    rhs = handle (first (flip f) <$> x) (flip ($) <$> y)

-- P1: handle x (pure y) == either y id <$> x
p1 :: Selective f => f (Either a b) -> (a -> b) -> f b
p1 x y = lhs === rhs
  where
    lhs = handle x (pure y)
    rhs = either y id <$> x

-- P2: handle (pure (Left x)) y = ($x) <$> y
p2 :: Selective f => a -> f (a -> b) -> f b
p2 x y = lhs === rhs
  where
    lhs = handle (pure (Left x)) y
    rhs = ($x) <$> y

-- A1: handle x (handle y z) = handle (handle (f <$> x) (g <$> y)) (h <$> z)
--       where f x = Right <$> x
--             g y = \a -> bimap (,a) ($a) y
--             h z = uncurry z
a1 :: Selective f => f (Either a b) -> f (Either c (a -> b)) -> f (c -> a -> b) -> f b
a1 x y z = lhs === rhs
  where
    lhs = handle x (handle y z)
    rhs = handle (handle (f <$> x) (g <$> y)) (h <$> z)
    f x = Right <$> x
    g y = \a -> bimap (,a) ($a) y
    h z = uncurry z

-- Now let's typecheck some theorems

-- Identity: pure id <*> v = v
t1 :: Selective f => f a -> f a
t1 v = s1 === s2 === s3 === s4 === s5 === s6
  where
    -- Step 1: Express the lefthand side using 'apS'
    s1 = apS (pure id) v
    -- Step 2: Definition of 'apS'
    s2 = handle (Left <$> pure id) (flip ($) <$> v)
    -- Step 3: Push 'Left' inside 'pure'
    s3 = handle (pure (Left id)) (flip ($) <$> v)
    -- Step 4: Apply P2
    s4 = ($id) <$> (flip ($) <$> v)
    -- Step 5: Simplify
    s5 = id <$> v
    -- Step 6: Functor identity: fmap id = id
    s6 = v

-- Homomorphism: pure f <*> pure x = pure (f x)
t2 :: Selective f => (a -> b) -> a -> f b
t2 f x = s1 === s2 === s3 === s4 === s5 === s6
  where
    -- Step 1: Express the lefthand side using 'apS'
    s1 = apS (pure f) (pure x)
    -- Step 2: Definition of 'apS'
    s2 = handle (Left <$> pure f) (flip ($) <$> pure x)
    -- Step 3: Push 'Left' inside 'pure'
    s3 = handle (pure (Left f)) (flip ($) <$> pure x)
    -- Step 4: Apply P2
    s4 = ($f) <$> (flip ($) <$> pure x)
    -- Step 5: Simplify
    s5 = f <$> pure x
    -- Step 6: Apply a pure function to a pure value (pure f <*> pure x)
    s6 = pure (f x)

-- Interchange: u <*> pure y = pure ($y) <*> u
t3 :: Selective f => f (a -> b) -> a -> f b
t3 u y = s1 === s2 === s3 === s4 === s5 === s6 === s7 === s8 === s9 === s10
  where
    -- Step 1: Express the lefthand side using 'apS'
    s1 = apS u (pure y)
    -- Step 2: Definition of 'apS'
    s2 = handle (Left <$> u) (flip ($) <$> pure y)
    -- Step 3: Rewrite to have a pure handler
    s3 = handle (Left <$> u) (pure ($y))
    -- Step 4: Apply P1
    s4 = either ($y) id <$> (Left <$> u)
    -- Step 5: Simplify
    s5 = ($y) <$> u

    -- Step 6: Express right-hand side of the theorem using 'apS'
    s6 = apS (pure ($y)) u
    -- Step 7: Definition of 'apS'
    s7 = handle (Left <$> pure ($y)) (flip ($) <$> u)
    -- Step 8: Push 'Left' inside 'pure'
    s8 = handle (pure (Left ($y))) (flip ($) <$> u)
    -- Step 9: Apply P2
    s9 = ($($y)) <$> (flip ($) <$> u)
    -- Step 10: Simplify, obtaining the 's10' = 's5'.
    s10 = ($y) <$> u

-- Composition: (.) <$> u <*> v <*> w = u <*> (v <*> w)
t4 :: Selective f => f (b -> c) -> f (a -> b) -> f a -> f c
t4 u v w = lhs === rhs
  where
    -- Rewrite the lefthand side:
    lhs = s1 === s2 === s3 === s4 === s5 === s6 === s7
    -- Step 1: Express the lefthand side using 'apS'
    s1 = apS (apS ((.) <$> u) v) w
    -- Step 2: Definition of 'apS'
    s2 = handle (Left <$> handle (Left <$> (.) <$> u) (flip ($) <$> v)) (flip ($) <$> w)
    -- Step 3: Apply F1 to push the leftmost 'Left' inside 'handle'
    s3 = handle (handle (second Left <$> Left <$> (.) <$> u) ((Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    -- Step 4: Simplify
    s4 = handle (handle (Left <$> (.) <$> u) ((Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    -- Step 5: Pull (.) outside 'Left'
    s5 = handle (handle (first (.) <$> Left <$> u) ((Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    -- Step 6: Apply F2 to push @(.)@ to the handler
    s6 = handle (handle (Left <$> u) ((. (.)) <$> (Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    -- Step 7: Simplify
    s7 = handle (handle (Left <$> u) ((Left .) <$> flip (.) <$> v)) (flip ($) <$> w)

    -- Rewrite the righthand side:
    rhs = s8 === s9 === s10 === s11 === s12 === s13 === s14 === s15 === s16
    -- Step 8: Express the righthand side using 'apS'
    s8 = apS u (apS v w)
    -- Step 9: Definition of 'apS'
    s9 = handle (Left <$> u) (flip ($) <$> handle (Left <$> v) (flip ($) <$> w))
    -- Step 10: Apply F1 to push @flip ($)@ inside 'handle'
    s10 = handle (Left <$> u) (handle (Left <$> v) ((flip ($) .) <$> flip ($) <$> w))
    -- Step 11: Apply A1 to reassociate to the left
    s11 = handle (handle (Left <$> u) ((\y a -> bimap (,a) ($a) y) <$> Left <$> v)) (uncurry . (flip ($) .) <$> flip ($) <$> w)
    -- Step 12: Simplify
    s12 = handle (handle (Left <$> u) ((\y a -> Left (y, a)) <$> v)) ((\x (f, g) -> g (f x)) <$> w)
    -- Step 13: Apply F3 to pull the rightmost pure function inside 'handle'
    s13 = handle (first (flip ((\x (f, g) -> g (f x)))) <$> handle (Left <$> u) ((\y a -> Left (y, a)) <$> v)) (flip ($) <$> w)
    -- Step 14: Simplify
    s14 = handle (first (\(f, g) -> g . f) <$> handle (Left <$> u) ((\y a -> Left (y, a)) <$> v)) (flip ($) <$> w)
    -- Step 15: Apply F1 to push the leftmost pure function inside 'handle'
    s15 = handle (handle (Left <$> u) (((first (\(f, g) -> g . f)).) <$> (\y a -> Left (y, a)) <$> v)) (flip ($) <$> w)
    -- Step 16: Simplify, obtaining the 's16' = 's7'.
    s16 = handle (handle (Left <$> u) ((Left .) <$> flip (.) <$> v)) (flip ($) <$> w)

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
