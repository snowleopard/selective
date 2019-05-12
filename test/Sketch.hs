{-# LANGUAGE FlexibleInstances, GADTs, RankNTypes, ScopedTypeVariables, TupleSections #-}
module Sketch where

import Control.Arrow hiding (first, second)
import Control.Category (Category)
import Control.Monad
import Control.Selective
import Data.Bifunctor
import Data.Void

import qualified Control.Arrow    as A
import qualified Control.Category as C

-- This file contains various examples and proof sketches and we keep it here to
-- make sure it still compiles.

------------------------------- Various examples -------------------------------

bindBool :: Selective f => f Bool -> (Bool -> f a) -> f a
bindBool x f = ifS x (f False) (f True)

branch3 :: Selective f => f (Either a (Either b c)) -> f (a -> d) -> f (b -> d) -> f (c -> d) -> f d
branch3 x a b c = (fmap (fmap Left)     <$> x)
              <*? (fmap (Right . Right) <$> a)
              <*? (fmap Right           <$> b)
              <*? c

bindOrdering :: Selective f => f Ordering -> (Ordering -> f a) -> f a
bindOrdering x f = branch3 (toEither <$> x) (const <$> f LT) (const <$> f EQ) (const <$> f GT)
  where
    toEither LT = Left ()
    toEither EQ = Right (Left ())
    toEither GT = Right (Right ())

-------------------------------- Proof sketches --------------------------------
-- A convenient primitive which checks that the types of two given values
-- coincide and returns the first value.
(===) :: a -> a -> a
x === y = if True then x else y

infixl 0 ===

-- First, we typecheck the laws

-- F1 (Free): f <$> select x y = select (fmap f <$> x) (fmap f <$> y)
f1 :: Selective f => (b -> c) -> f (Either a b) -> f (a -> b) -> f c
f1 f x y = f <$> select x y === select (fmap f <$> x) (fmap f <$> y)

-- F2 (Free): select (first f <$> x) y = select x ((. f) <$> y)
f2 :: Selective f => (a -> c) -> f (Either a b) -> f (c -> b) -> f b
f2 f x y = select (first f <$> x) y === select x ((. f) <$> y)

-- F3 (Free): select x (f <$> y) = select (first (flip f) <$> x) (flip ($) <$> y)
f3 :: Selective f => (c -> a -> b) -> f (Either a b) -> f c -> f b
f3 f x y = select x (f <$> y) === select (first (flip f) <$> x) (flip ($) <$> y)

-- P1 (Generalised identity): select x (pure y) == either y id <$> x
p1 :: Selective f => f (Either a b) -> (a -> b) -> f b
p1 x y = select x (pure y) === either y id <$> x

-- A more basic form of P1, from which P1 itself follows as a free theorem.
-- Intuitively, both 'p1' and 'p1id' make the following Const instance illegal:
--
-- @
-- instance Monoid m => Selective (Const m) where
--    select (Const x) (Const _) = Const (x <> x)
-- @
-- P1id (Identity): select x (pure id) == either id id <$> x
p1id  :: Selective f => f (Either a a) -> f a
p1id x = select x (pure id) === either id id <$> x

-- P2 (does not generally hold): select (pure (Left x)) y = ($x) <$> y
p2 :: Selective f => a -> f (a -> b) -> f b
p2 x y = select (pure (Left  x)) y === y <*> pure x

-- P3 (does not generally hold): select (pure (Right x)) y = pure x
p3 :: Selective f => b -> f (a -> b) -> f b
p3 x y = select (pure (Right x)) y === pure x

-- A1 (Associativity):
--     select x (select y z) = select (select (f <$> x) (g <$> y)) (h <$> z)
--       where f x = Right <$> x
--             g y = \a -> bimap (,a) ($a) y
--             h z = uncurry z
a1 :: Selective f => f (Either a b) -> f (Either c (a -> b)) -> f (c -> a -> b) -> f b
a1 x y z = select x (select y z) === select (select (f <$> x) (g <$> y)) (h <$> z)
  where
    f x = Right <$> x
    g y = \a -> bimap (,a) ($a) y
    h z = uncurry z

-- Intuitively, 'i1' makes the following Const instance illegal, by insisting
-- that effects on the left hand side must be executed.
--
-- @
-- instance Monoid m => Selective (Const m) where
--    select _ _ = Const mempty
-- @
--
-- If we decompose an effect @x :: f a@ into the effect itself @void x@ and the
-- resulting pure value @a@, i.e. @void x *> pure a@, then it becomes clear that
-- 'i1unit' means that all effects must be executed and the remainig pure value
-- will be used to select whether to execute or skip the right hand side.
-- i1unit (Interchange): (x *> y) <*? z = x *> (y <*? z)
i1unit :: Selective f => f c -> f (Either a b) -> f (a -> b) -> f b
i1unit x y z =
    (x *> y) <*? z
    ===
    x *> (y <*? z)

-- i1: x <*> (y <*? z) = (f <$> x <*> y) <*? (g <$> z)
--     where
--       f = (\ab -> bimap (, ab) ab)
--       g = (\ca (c, ab) -> ab (ca c))
i1 :: Selective f => f (a -> b) -> f (Either c a) -> f (c -> a) -> f b
i1 x y z =
    x <*> (y <*? z)
    ===
    (f <$> x <*> y) <*? (g <$> z)
  where
    f ab = bimap (\c ca -> ab (ca c)) ab
    g ca = ($ca)

-- D1 (distributivity): pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z)
d1 :: Selective f => Either a b -> f (a -> b) -> f (a -> b) -> f b
d1 x y z =
    pure x <*? (y *> z)
    ===
    (pure x <*? y) *> (pure x <*? z)

-- TODO: Can we prove the following from D1?
-- ifS (pure x) a1 b1 *> ifS (pure x) a2 b2 = ifS (pure x) (a1 *> a2) (b1 *> b2)

-- Now let's typecheck some theorems

-- This assumes P2, which does not always hold
-- Identity: pure id <*> v = v
t1 :: Selective f => f a -> f a
t1 v =
    -- Express the lefthand side using 'apS'
    apS (pure id) v
    === -- Definition of 'apS'
    select (Left <$> pure id) (flip ($) <$> v)
    === -- Push 'Left' inside 'pure'
    select (pure (Left id)) (flip ($) <$> v)
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
    select (Left <$> pure f) (flip ($) <$> pure x)
    === -- Push 'Left' inside 'pure'
    select (pure (Left f)) (flip ($) <$> pure x)
    === -- Applicative's fmap-pure law
    select (pure (Left f)) (pure (flip ($) x))
    === -- Apply P1
    either ((flip ($) x)) id <$> pure (Left f)
    === -- Applicative's fmap-pure law
    pure ((flip ($) x) f)
    === -- Simplify
    pure (f x)

-- This assumes P2, which does not always hold
-- Interchange: u <*> pure y = pure ($y) <*> u
t3 :: Selective f => f (a -> b) -> a -> f b
t3 u y =
    -- Express the lefthand side using 'apS'
    apS u (pure y)
    === -- Definition of 'apS'
    select (Left <$> u) (flip ($) <$> pure y)
    === -- Rewrite to have a pure second argument
    select (Left <$> u) (pure ($y))
    === -- Apply P1
    either ($y) id <$> (Left <$> u)
    === -- Simplify, obtaining (#)
    ($y) <$> u

    === -- Express right-hand side of the theorem using 'apS'
    apS (pure ($y)) u
    === -- Definition of 'apS'
    select (Left <$> pure ($y)) (flip ($) <$> u)
    === -- Push 'Left' inside 'pure'
    select (pure (Left ($y))) (flip ($) <$> u)
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
    select (Left <$> select (Left <$> (.) <$> u) (flip ($) <$> v)) (flip ($) <$> w)
    === -- Apply F1 to push the leftmost 'Left' inside 'select'
    select (select (second Left <$> Left <$> (.) <$> u) ((Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    === -- Simplify
    select (select (Left <$> (.) <$> u) ((Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    === -- Pull (.) outside 'Left'
    select (select (first (.) <$> Left <$> u) ((Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    === -- Apply F2 to push @(.)@ to the function
    select (select (Left <$> u) ((. (.)) <$> (Left .) <$> flip ($) <$> v)) (flip ($) <$> w)
    === -- Simplify, obtaining (#)
    select (select (Left <$> u) ((Left .) <$> flip (.) <$> v)) (flip ($) <$> w)

    === -- Express the righthand side using 'apS'
    apS u (apS v w)
    === -- Definition of 'apS'
    select (Left <$> u) (flip ($) <$> select (Left <$> v) (flip ($) <$> w))
    === -- Apply F1 to push @flip ($)@ inside 'select'
    select (Left <$> u) (select (Left <$> v) ((flip ($) .) <$> flip ($) <$> w))
    === -- Apply A1 to reassociate to the left
    select (select (Left <$> u) ((\y a -> bimap (,a) ($a) y) <$> Left <$> v)) (uncurry . (flip ($) .) <$> flip ($) <$> w)
    === -- Simplify
    select (select (Left <$> u) ((\y a -> Left (y, a)) <$> v)) ((\x (f, g) -> g (f x)) <$> w)
    === -- Apply F3 to pull the rightmost pure function inside 'select'
    select (first (flip ((\x (f, g) -> g (f x)))) <$> select (Left <$> u) ((\y a -> Left (y, a)) <$> v)) (flip ($) <$> w)
    === -- Simplify
    select (first (\(f, g) -> g . f) <$> select (Left <$> u) ((\y a -> Left (y, a)) <$> v)) (flip ($) <$> w)
    === -- Apply F1 to push the leftmost pure function inside 'select'
    select (select (Left <$> u) (((first (\(f, g) -> g . f)).) <$> (\y a -> Left (y, a)) <$> v)) (flip ($) <$> w)
    === -- Simplify, obtaining (#)
    select (select (Left <$> u) ((Left .) <$> flip (.) <$> v)) (flip ($) <$> w)

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

biselect :: Selective f => f (Either a b) -> f (Either a c) -> f (Either a (b, c))
biselect x y = select ((fmap Left . swapEither) <$> x) ((\e a -> fmap (a,) e) <$> y)

(?*?) :: Selective f => f (Either a b) -> f (Either a c) -> f (Either a (b, c))
(?*?) = biselect

a1M :: Selective f => f (Either a b) -> f (Either a c) -> f (Either a d)
                   -> f (Either a (b, (c, d)))
a1M x y z =
    x ?*? (y ?*? z)
    ===
    second assoc <$> ((x ?*? y) ?*? z)
  where
    assoc ((a, b), c) = (a, (b, c))

apM :: SelectiveM f => f (a -> b) -> f a -> f b
apM f x = fmap (either absurd (uncurry ($))) (fmap Right f |**| fmap Right x)

fromM :: SelectiveM f => f (Either a b) -> f (a -> b) -> f b
fromM x f = either id (\(a, f) -> f a) <$> (fmap swapEither x |**| fmap Right f)

toM :: Selective f => f (Either e a) -> f (Either e b) -> f (Either e (a, b))
toM a b = select ((fmap Left . swapEither) <$> a) ((\e a -> fmap (a,) e) <$> b)

-- | Swap @Left@ and @Right@.
swapEither :: Either a b -> Either b a
swapEither = either Right Left

-- Proof that if select = selectM, and <*> = ap, then <*> = apS.
apSEqualsApply :: (Selective f, Monad f) => f (a -> b) -> f a -> f b
apSEqualsApply fab fa =
    fab <*> fa
    === -- Law: <*> = ap
    ap fab fa
    === -- Free theorem (?)
    selectM (Left <$> fab) (flip ($) <$> fa)
    === -- Law: selectM = select
    select (Left <$> fab) (flip ($) <$> fa)
    === -- Definition of apS
    apS fab fa

-- | Selective function composition, where the first effect is always evaluated,
-- but the second one can be skipped if the first value is @Nothing@.
-- Thanks to the laws of 'Selective', this operator is associative, and has
-- identity @pure (Just id)@.
(.?) :: Selective f => f (Maybe (b -> c)) -> f (Maybe (a -> b)) -> f (Maybe (a -> c))
x .? y = select (maybe (Right Nothing) Left <$> x) ((\ab bc -> (bc .) <$> ab) <$> y)

infixl 4 .?

-- This assumes P2, which does not always hold
-- Proof of left identity: pure (Just id) .? x = x
t5 :: Selective f => f (Maybe (a -> b)) -> f (Maybe (a -> b))
t5 x =
    --- Lefthand side
    pure (Just id) .? x
    === -- Express the lefthand side by expanding the definition of '.?'
    select (maybe (Right Nothing) Left <$> pure (Just id))
        ((\ab bc -> (bc .) <$> ab) <$> x)
    === -- Simplify
    select (pure $ Left id) ((\ab bc -> (bc .) <$> ab) <$> x)
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
    select (maybe (Right Nothing) Left <$> x)
        ((\ab bc -> (bc .) <$> ab) <$> pure (Just id))
    === -- Simplify
    select (maybe (Right Nothing) Left <$> x) (pure Just)
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
    select (maybe (Right Nothing) Left <$> (select (maybe (Right Nothing) Left <$> x)
        ((\ab bc -> (bc .) <$> ab) <$> y)))
        ((\ab bc -> (bc .) <$> ab) <$> z)
    === -- Apply F3 to move the rightmost pure function into the outer 'select'
    select (first (flip $ (\ab bc -> (bc .) <$> ab)) <$> maybe (Right Nothing) Left <$> (select (maybe (Right Nothing) Left <$> x)
        ((\ab bc -> (bc .) <$> ab) <$> y)))
        (flip ($) <$> z)
    === -- Simplify
    select (maybe (Right Nothing) (\bc -> Left $ fmap $ (bc .)) <$> (select (maybe (Right Nothing) Left <$> x)
        ((\ab bc -> (bc .) <$> ab) <$> y)))
        (flip ($) <$> z)
    === -- Apply F1 to move the pure function into the inner 'select'
    select (select (second (maybe (Right Nothing) (\bc -> Left $ fmap $ (bc .))) <$> maybe (Right Nothing) Left <$> x)
        (((maybe (Right Nothing) (\bc -> Left $ fmap $ (bc .))).) <$> (\ab bc -> (bc .) <$> ab) <$> y))
        (flip ($) <$> z)
    === -- Simplify, obtaining (#)
    select (select (maybe (Right (Right Nothing)) Left <$> x)
        ((\mbc cd -> maybe (Right Nothing) (\bc -> Left $ fmap ((cd . bc) .)) mbc) <$> y))
        (flip ($) <$> z)

    === -- Righthand side
    x .? (y .? z)
    === -- Express the righthand side by expanding the definition of '.?'
    select (maybe (Right Nothing) Left <$> x)
        ((\ab bc -> (bc .) <$> ab) <$> (select (maybe (Right Nothing) Left <$> y)
        ((\ab bc -> (bc .) <$> ab) <$> z)))
    === -- Apply F1 to move the pure function into the inner 'select'
    select (maybe (Right Nothing) Left <$> x)
        (select (second ((\ab bc -> (bc .) <$> ab)) <$> maybe (Right Nothing) Left <$> y)
        ((((\ab bc -> (bc .) <$> ab)).) <$> (\ab bc -> (bc .) <$> ab) <$> z))
    === -- Apply A1 to reassociate to the left
    select (select (fmap Right <$> maybe (Right Nothing) Left <$> x)
        ((\y a -> bimap (,a) ($a) y) <$> second ((\ab bc -> (bc .) <$> ab)) <$> maybe (Right Nothing) Left <$> y))
        (uncurry <$> (((\ab bc -> (bc .) <$> ab)).) <$> (\ab bc -> (bc .) <$> ab) <$> z)
    === -- Simplify
    select (select (maybe (Right (Right Nothing)) Left <$> x)
        ((\m a -> maybe (Right Nothing) (Left . (,a)) m) <$> y))
        ((\ab (bc, cd) -> ((cd . bc) .) <$> ab) <$> z)
    === -- Apply F3 to move the rightmost pure function into the outer 'select'
    select (first (flip $ \ab (bc, cd) -> ((cd . bc) .) <$> ab) <$> select (maybe (Right (Right Nothing)) Left <$> x)
        ((\m a -> maybe (Right Nothing) (Left . (,a)) m) <$> y))
        (flip ($) <$> z)
    === -- Apply F1 to move the pure function into the inner 'select', obtaining (#)
    select (select (maybe (Right (Right Nothing)) Left <$> x)
        ((\mbc cd -> maybe (Right Nothing) (\bc -> Left $ fmap ((cd . bc) .)) mbc) <$> y))
        (flip ($) <$> z)


------------------------ Carter Schonwald's copatterns -------------------------
-- See: https://github.com/cartazio/symmetric-monoidal/blob/15b209953b7d4a47651f615b02dbb0171de8af40/src/Control/Monoidal.hs#L93
-- And also: https://twitter.com/andreymokhov/status/1102648479841701888

data Choose a b c where
    CLeft  :: Choose a b a
    CRight :: Choose a b b

newtype Choice a b = Choice (forall r . Choose a b r -> r)

class SelectiveC f where
    choose :: f (Either a b) -> Choice (f (a -> c)) (f (b -> c)) -> f c

-- Recover selective 'branch' from 'choose'.
branchC :: SelectiveC f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branchC x l r = choose x $ Choice $ \c -> case c of { CLeft -> l; CRight -> r }

-- Recover 'choose' from selective 'branch'.
chooseS :: Selective f => f (Either a b) -> Choice (f (a -> c)) (f (b -> c)) -> f c
chooseS x (Choice c) = branch x (c CLeft) (c CRight)

------------------------------- Free ArrowChoice -------------------------------

-- A free 'ArrowChoice' built on top of base components @f i o@.
newtype FreeArrowChoice f a b = FreeArrowChoice {
    runFreeArrowChoice :: forall arr. ArrowChoice arr =>
        (forall i o. f i o -> arr i o) -> arr a b }

instance Category (FreeArrowChoice f) where
    id = FreeArrowChoice (\_ -> C.id)
    FreeArrowChoice x . FreeArrowChoice y = FreeArrowChoice (\t -> x t C.. y t)

instance Arrow (FreeArrowChoice f) where
    arr x = FreeArrowChoice (\_ -> A.arr x)
    first (FreeArrowChoice x) = FreeArrowChoice (\t -> A.first (x t))

instance ArrowChoice (FreeArrowChoice f) where
    left (FreeArrowChoice x) = FreeArrowChoice (\t -> A.left (x t))

-- A constant arrow, similar to the 'Const' applicative functor.
newtype ConstArrow m a b = ConstArrow { getConstArrow :: m }

instance Monoid m => Category (ConstArrow m) where
    id = ConstArrow mempty
    ConstArrow x . ConstArrow y = ConstArrow (mappend x y)

instance Monoid m => Arrow (ConstArrow m) where
    arr _ = ConstArrow mempty
    first (ConstArrow x) = ConstArrow x

instance Monoid m => ArrowChoice (ConstArrow m) where
    left (ConstArrow x) = ConstArrow x

-- Collect all base arrows in a 'FreeArrowChoice'.
foldArrowChoice :: Monoid m => (forall i o. f i o -> m) -> FreeArrowChoice f a b -> m
foldArrowChoice f arr = getConstArrow $ runFreeArrowChoice arr (ConstArrow . f)

-- Execute a 'FreeArrowChoice' in an arbitrary monad.
runArrowChoice :: Monad m => (forall i o. f i o -> (i -> m o)) -> FreeArrowChoice f a b -> (a -> m b)
runArrowChoice f arr = runKleisli $ runFreeArrowChoice arr (Kleisli . f)
