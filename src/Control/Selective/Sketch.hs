{-# LANGUAGE TupleSections, ScopedTypeVariables #-}
module Control.Selective.Sketch where

import Control.Selective
import Data.Bifunctor

-------------------------------- Proof sketches --------------------------------

-- A convenient primitive which checks that the types of two given values
-- coincide and returns the first value.
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
    === -- Functor identity: -- Functor identity: fmap id = id
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

-- Alternative type classes for selective functors. They all come with an
-- additional requirement that we run effects from left to right.

-- Composition of Applicative and Either monad
class Applicative f => SelectiveA f where
    (|*|) :: f (Either e (a -> b)) -> f (Either e a) -> f (Either e b)

-- Composition of Starry and Either monad
-- See: https://duplode.github.io/posts/applicative-archery.html
class Applicative f => SelectiveS f where
    (|.|) :: f (Either e (b -> c)) -> f (Either e (a -> b)) -> f (Either e (a -> c))

-- Composition of Monoidal and Either monad
-- See: http://blog.ezyang.com/2012/08/applicative-functors/
class Applicative f => SelectiveM f where
    (|**|) :: f (Either e a) -> f (Either e b) -> f (Either e (a, b))

-- | Selective function composition, where the first effect is always evaluated,
-- but the second one can be skipped if the first value is @Nothing@.
-- Thanks to the laws of 'Selective', this operator is associative, and has
-- identity @pure (Just id)@.
(.?) :: Selective f => f (Maybe (b -> c)) -> f (Maybe (a -> b)) -> f (Maybe (a -> c))
x .? y = handle (maybe (Right Nothing) Left <$> x) ((\ab bc -> (bc .) <$> ab) <$> y)

infixl 4 .?

-- Proof of left identity: pure (Just id) .? x = x
t5 :: Selective f => f (Maybe (a -> b)) -> f (Maybe (a -> b))
t5 x =
    --- Lefthand side
    pure (Just id) .? x
    === -- Express the lefthand side by expanding the definition of '.?'
    handle (maybe (Right Nothing) Left <$> pure (Just id))
        ((\ab bc -> (bc .) <$> ab) <$> x)
    === -- Simplify
    handle (pure $ Left id) ((\ab bc -> (bc .) <$> ab) <$> x)
    === -- Apply P2
    ($id) <$> ((\ab bc -> (bc .) <$> ab) <$> x)
    === -- Simplify
    (($id) <$> (\ab bc -> (bc .) <$> ab) <$> x)
    === -- Functor identity: fmap id = id
    id <$> x
    ===
    x

-- Proof of right identity: x .? pure (Just id) = x
t6 :: Selective f => f (Maybe (a -> b)) -> f (Maybe (a -> b))
t6 x =
    --- Lefthand side
    x .? pure (Just id)
    === -- Express the lefthand side by expanding the definition of '.?'
    handle (maybe (Right Nothing) Left <$> x)
        ((\ab bc -> (bc .) <$> ab) <$> pure (Just id))
    === -- Simplify
    handle (maybe (Right Nothing) Left <$> x) (pure Just)
    === -- Apply P1
    either Just id <$> (maybe (Right Nothing) Left <$> x)
    === -- Functor identity: fmap id = id
    id <$> x
    ===
    x

-- Proof of associativity: (x .? y) .? z = x .? (y .? z)
t7 :: Selective f => f (Maybe (c -> d)) -> f (Maybe (b -> c)) -> f (Maybe (a -> b)) -> f (Maybe (a -> d))
t7 x y z =
    -- Lefthand side
    (x .? y) .? z
    === -- Express the lefthand side by expanding the definition of '.?'
    handle (maybe (Right Nothing) Left <$> (handle (maybe (Right Nothing) Left <$> x)
        ((\ab bc -> (bc .) <$> ab) <$> y)))
        ((\ab bc -> (bc .) <$> ab) <$> z)
    === -- Apply F3 to move the rightmost pure function into the outer 'handle'
    handle (first (flip $ (\ab bc -> (bc .) <$> ab)) <$> maybe (Right Nothing) Left <$> (handle (maybe (Right Nothing) Left <$> x)
        ((\ab bc -> (bc .) <$> ab) <$> y)))
        (flip ($) <$> z)
    === -- Simplify
    handle (maybe (Right Nothing) (\bc -> Left $ fmap $ (bc .)) <$> (handle (maybe (Right Nothing) Left <$> x)
        ((\ab bc -> (bc .) <$> ab) <$> y)))
        (flip ($) <$> z)
    === -- Apply F1 to move the pure function into the inner 'handle'
    handle (handle (second (maybe (Right Nothing) (\bc -> Left $ fmap $ (bc .))) <$> maybe (Right Nothing) Left <$> x)
        (((maybe (Right Nothing) (\bc -> Left $ fmap $ (bc .))).) <$> (\ab bc -> (bc .) <$> ab) <$> y))
        (flip ($) <$> z)
    === -- Simplify, obtaining (#)
    handle (handle (maybe (Right (Right Nothing)) Left <$> x)
        ((\mbc cd -> maybe (Right Nothing) (\bc -> Left $ fmap ((cd . bc) .)) mbc) <$> y))
        (flip ($) <$> z)

    === -- Righthand side
    x .? (y .? z)
    === -- Express the righthand side by expanding the definition of '.?'
    handle (maybe (Right Nothing) Left <$> x)
        ((\ab bc -> (bc .) <$> ab) <$> (handle (maybe (Right Nothing) Left <$> y)
        ((\ab bc -> (bc .) <$> ab) <$> z)))
    === -- Apply F1 to move the pure function into the inner 'handle'
    handle (maybe (Right Nothing) Left <$> x)
        (handle (second ((\ab bc -> (bc .) <$> ab)) <$> maybe (Right Nothing) Left <$> y)
        ((((\ab bc -> (bc .) <$> ab)).) <$> (\ab bc -> (bc .) <$> ab) <$> z))
    === -- Apply A1 to reassociate to the left
    handle (handle (fmap Right <$> maybe (Right Nothing) Left <$> x)
        ((\y a -> bimap (,a) ($a) y) <$> second ((\ab bc -> (bc .) <$> ab)) <$> maybe (Right Nothing) Left <$> y))
        (uncurry <$> (((\ab bc -> (bc .) <$> ab)).) <$> (\ab bc -> (bc .) <$> ab) <$> z)
    === -- Simplify
    handle (handle (maybe (Right (Right Nothing)) Left <$> x)
        ((\m a -> maybe (Right Nothing) (Left . (,a)) m) <$> y))
        ((\ab (bc, cd) -> ((cd . bc) .) <$> ab) <$> z)
    === -- Apply F3 to move the rightmost pure function into the outer 'handle'
    handle (first (flip $ \ab (bc, cd) -> ((cd . bc) .) <$> ab) <$> handle (maybe (Right (Right Nothing)) Left <$> x)
        ((\m a -> maybe (Right Nothing) (Left . (,a)) m) <$> y))
        (flip ($) <$> z)
    === -- Apply F1 to move the pure function into the inner 'handle', obtaining (#)
    handle (handle (maybe (Right (Right Nothing)) Left <$> x)
        ((\mbc cd -> maybe (Right Nothing) (\bc -> Left $ fmap ((cd . bc) .)) mbc) <$> y))
        (flip ($) <$> z)

-- Various generalised versions of handle and select

handle2 :: Selective f => f (Either a (Either b r)) -> f (a -> r) -> f (b -> r) -> f r
handle2 x ar br = handle (handle x ((Right.) <$> ar)) br

handle3 :: Selective f => f (Either a (Either b (Either c r)))
        -> f (a -> r) -> f (b -> r) -> f (c -> r) -> f r
handle3 x ar = handle2 (handle x (((Right . Right).) <$> ar))

handle4 :: Selective f => f (Either a (Either b (Either c (Either d r))))
        -> f (a -> r) -> f (b -> r) -> f (c -> r) -> f (d -> r) -> f r
handle4 x ar = handle3 (handle x (((Right . Right . Right).) <$> ar))

select4 :: Selective f => f (Either (Either a b) (Either c d))
        -> f (a -> e) -> f (b -> e) -> f (c -> e) -> f (d -> e) -> f e
select4 x = handle4 (rotateEither <$> x)

rotateEither :: Either (Either a b) (Either c d)
             -> Either a (Either b (Either c (Either d e)))
rotateEither (Left (Left a)) = Left a
rotateEither (Left (Right b)) = Right (Left b)
rotateEither (Right (Left c)) = Right (Right (Left c))
rotateEither (Right (Right d)) = Right (Right (Right (Left d)))

bindTwoBools :: Selective f => f (Bool, Bool) -> ((Bool, Bool) -> f a) -> f a
bindTwoBools xy f = select4 (toEither2 <$> xy) (const <$> f (False, False))
                                               (const <$> f (False,  True))
                                               (const <$> f (True , False))
                                               (const <$> f (True ,  True))
  where
    toEither2 (x, y) = toEither x $ toEither y ()

toEither :: Bool -> a -> Either a a
toEither True  = Right
toEither False = Left

-- Goals:
-- bindBools :: Selective f => f [Bool] -> ([Bool] -> f a) -> f a
-- bindS :: (Binary a, Selective f) => f a -> (a -> f b) -> f b
