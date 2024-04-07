{-# LANGUAGE DeriveFunctor, GADTs, RankNTypes, TupleSections, TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables, LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Selective.Multi
-- Copyright  : (c) Andrey Mokhov 2018-2024
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- This is a library for /selective applicative functors/, or just
-- /selective functors/ for short, an abstraction between applicative functors
-- and monads, introduced in this paper: https://dl.acm.org/doi/10.1145/3341694.
--
-- This module defines /multi-way selective functors/, which are more efficient
-- when selecting from a large number of options. They also fully subsume the
-- 'Applicative' type class because they allow to express the notion of
-- independet effects.
--
-- This definition is inspired by the following construction by Daniel Peebles,
-- with the main difference being the added @Enumerable@ constraint:
-- https://gist.github.com/copumpkin/d5bdbc7afda54ff04049b6bdbcffb67e
--
-----------------------------------------------------------------------------
module Control.Selective.Multi (
    -- * Generalised sum types
    Sigma (..), inject, Zero, One (..), Two (..), Many (..), many, matchPure,
    eitherToSigma, sigmaToEither,

    -- * Selective functors
    Some (..), Enumerable (..), Selective (..), Over (..), Under (..), select,
    branch, apS, bindS,

    -- * Applicative functors
    ApplicativeS (..), ap, matchA,

    -- * Monads
    MonadS (..), bind, matchM,

    -- * Generalised products and various combinators
    type (~>), Pi, project, identity, compose, apply, toSigma, fromSigma, toPi,
    fromPi, pairToPi, piToPair, Case (..), matchCases,
    ) where

import Control.Applicative ((<**>))
import Data.Functor.Identity

------------------------ Meet two friends: Sigma and Pi ------------------------
-- | A generalised sum type where @t@ stands for the type of constructor "tags".
-- Each tag has a type parameter @x@ which determines the type of the payload.
-- A 'Sigma' @t@ value therefore contains a payload whose type is not visible
-- externally but is revealed when pattern-matching on the tag.
--
-- See 'Two', 'eitherToSigma' and 'sigmaToEither' for an example.
data Sigma t where
    Sigma :: t x -> x -> Sigma t

-- | An injection into a generalised sum. An alias for 'Sigma'.
inject :: t x -> x -> Sigma t
inject = Sigma

-- | A data type defining no tags. Similar to 'Data.Void.Void' but parameterised.
data Zero a where

-- | A data type with a single tag. This data type is commonly known as @Refl@,
-- see "Data.Type.Equality".
data One a b where
    One :: One a a

-- | A data type with two tags 'A' and 'B' that allows us to encode the good old
-- 'Either' as 'Sigma' 'Two', where the tags 'A' and 'B' correspond to 'Left'
-- and 'Right', respectively. See 'eitherToSigma' and 'sigmaToEither' that
-- witness the isomorphism between 'Either' @a b@ and 'Sigma' @(@'Two'@ a b)@.
data Two a b c where
    A :: Two a b a
    B :: Two a b b

-- | Encode 'Either' into a generalised sum type.
eitherToSigma :: Either a b -> Sigma (Two a b)
eitherToSigma = \case
    Left  a -> inject A a
    Right b -> inject B b

-- | Decode 'Either' from a generalised sum type.
sigmaToEither :: Sigma (Two a b) -> Either a b
sigmaToEither = \case
    Sigma A a -> Left  a
    Sigma B b -> Right b

-- | A potentially uncountable collection of tags for the same unit @()@ payload.
data Many a b where
    Many :: a -> Many a ()

many :: a -> Sigma (Many a)
many a = Sigma (Many a) ()

-- | Generalised pattern matching on a Sigma type using a Pi type to describe
-- how to handle each case.
--
-- This is a specialisation of 'matchCases' for @f = Identity@. We could also
-- have also given it the following type:
--
-- @
-- matchPure :: Sigma t -> (t ~> Case Identity a) -> a
-- @
--
-- We chose to simplify it by inlining '~>', 'Case' and 'Identity'.
matchPure :: Sigma t -> (forall x. t x -> x -> a) -> a
matchPure (Sigma t x) pi = pi t x

------------------------- Mutli-way selective functors -------------------------
-- | Hide the type of the payload a tag.
--
-- There is a whole library dedicated to this nice little GADT:
-- http://hackage.haskell.org/package/some.
data Some t where
    Some :: t a -> Some t

-- | A class of tags that can be enumerated.
--
-- A valid instance must list every tag in the resulting list exactly once.
class Enumerable t where
    enumerate :: [Some t]

instance Enumerable Zero where
    enumerate = []

instance Enumerable (One a) where
    enumerate = [Some One]

instance Enumerable (Two a b) where
    enumerate = [Some A, Some B]

instance Enum a => Enumerable (Many a) where
    enumerate = [ Some (Many x) | x <- enumFrom (toEnum 0) ]

-- | Multi-way selective functors. Given a computation that produces a value of
-- a sum type, we can 'match' it to the corresponding computation in a given
-- product type.
--
-- For greater similarity with 'matchCases', we could have given the following
-- type to 'match':
--
-- @
-- match :: f (Sigma t) -> (t ~> Case f a) -> f a
-- @
--
-- We chose to simplify it by inlining '~>' and 'Case'.
class Applicative f => Selective f where
    match :: Enumerable t => f (Sigma t) -> (forall x. t x -> f (x -> a)) -> f a

-- | The basic "if-then" selection primitive from "Control.Selective".
select :: Selective f => f (Either a b) -> f (a -> b) -> f b
select x f = match (eitherToSigma <$> x) $ \case
    A -> f
    B -> pure id

-- | Choose a matching effect with 'Either'.
branch :: Selective f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch x f g = match (eitherToSigma <$> x) $ \case
    A -> f
    B -> g

-- | Recover the application operator '<*>' from 'match'.
apS :: Selective f => f a -> f (a -> b) -> f b
apS x f = match (inject One <$> x) (\One -> f)

-- | A restricted version of monadic bind.
bindS :: (Enum a, Selective f) => f a -> (a -> f b) -> f b
bindS x f = match (many <$> x) (\(Many x) -> const <$> f x)

-- | Static analysis of selective functors with over-approximation.
newtype Over m a = Over { getOver :: m }
    deriving (Eq, Functor, Ord, Show)

instance Monoid m => Applicative (Over m) where
    pure _            = Over mempty
    Over x <*> Over y = Over (mappend x y)

instance Monoid m => Selective (Over m) where
    match (Over m) pi = Over (mconcat (m : ms))
      where
        ms = [ getOver (pi t) | Some t <- enumerate ]

-- | Static analysis of selective functors with under-approximation.
newtype Under m a = Under { getUnder :: m }
    deriving (Eq, Functor, Ord, Show)

instance Monoid m => Applicative (Under m) where
    pure _              = Under mempty
    Under x <*> Under y = Under (mappend x y)

instance Monoid m => Selective (Under m) where
    match (Under m) _ = Under m

-- | An alternative definition of applicative functors, as witnessed by 'ap' and
-- 'matchOne'. This class is almost like 'Selective' but has a strict constraint
-- on @t@.
class Functor f => ApplicativeS f where
    pureA    :: a -> f a
    matchOne :: t ~ One x => f (Sigma t) -> (forall x. t x -> f (x -> a)) -> f a

-- | Recover the application operator '<*>' from 'matchOne'.
ap :: ApplicativeS f => f a -> f (a -> b) -> f b
ap x f = matchOne (Sigma One <$> x) (\One -> f)

-- | Every 'Applicative' is also an 'ApplicativeS'.
matchA :: (Applicative f, t ~ One x) => f (Sigma t) -> (forall x. t x -> f (x -> a)) -> f a
matchA x pi = (\(Sigma One x) -> x) <$> x <**> pi One

-- | An alternative definition of monads, as witnessed by 'bind' and 'matchM'.
-- This class is almost like 'Selective' but has no the constraint on @t@.
class Applicative f => MonadS f where
    matchUnconstrained :: f (Sigma t) -> (forall x. t x -> f (x -> a)) -> f a

-- Adapted from the original implementation by Daniel Peebles:
-- https://gist.github.com/copumpkin/d5bdbc7afda54ff04049b6bdbcffb67e

-- | Monadic bind.
bind :: MonadS f => f a -> (a -> f b) -> f b
bind x f = matchUnconstrained (many <$> x) (\(Many x) -> const <$> f x)

-- | Every monad is a multi-way selective functor.
matchM :: Monad f => f (Sigma t) -> (forall x. t x -> f (x -> a)) -> f a
matchM sigma pi = sigma >>= \case Sigma t x -> ($x) <$> pi t

-- | A generalised product type (Pi), which holds an appropriately tagged
-- payload @u x@ for every possible tag @t x@.
--
-- Note that this looks different than the standard formulation of Pi types.
-- Maybe it's just all wrong!
--
-- See 'Two', 'pairToPi' and 'piToPair' for an example.
type (~>) t u = forall x. t x -> u x
infixl 4 ~>

-- | A product type where the payload has the type specified with the tag.
type Pi t = t ~> Identity

-- | A projection from a generalised product.
project :: t a -> Pi t -> a
project t pi = runIdentity (pi t)

-- | A trivial product type that stores nothing and simply returns the given tag
-- as the result.
identity :: t ~> t
identity = id

-- | As it turns out, one can compose such generalised products. Why not: given
-- a tag, get the payload of the first product and then pass it as input to the
-- second. This feels too trivial to be useful but is still somewhat cute.
compose :: (u ~> v) -> (t ~> u) -> (t ~> v)
compose f g = f . g

-- | Update a generalised sum given a generalised product that takes care of all
-- possible cases.
apply :: (t ~> u) -> Sigma t -> Sigma u
apply pi (Sigma t x) = Sigma (pi t) x

-- | Encode a value into a generalised sum type that has a single tag 'One'.
toSigma :: a -> Sigma (One a)
toSigma = inject One

-- | Decode a value from a generalised sum type that has a single tag 'One'.
fromSigma :: Sigma (One a) -> a
fromSigma (Sigma One a) = a

-- | Encode a value into a generalised product type that has a single tag 'One'.
toPi :: a -> Pi (One a)
toPi a One = Identity a

-- | Decode a value from a generalised product type that has a single tag 'One'.
fromPi :: Pi (One a) -> a
fromPi = project One

-- | Encode @(a, b)@ into a generalised product type.
pairToPi :: (a, b) -> Pi (Two a b)
pairToPi (a, b) = \case
    A -> Identity a
    B -> Identity b

-- | Decode @(a, b)@ from a generalised product type.
piToPair :: Pi (Two a b) -> (a, b)
piToPair pi = (project A pi, project B pi)

-- | Handler of a single case in a generalised pattern matching 'matchCases'.
newtype Case f a x = Case { handleCase :: f (x -> a) }

-- | Generalised pattern matching on a Sigma type using a Pi type to describe
-- how to handle each case.
matchCases :: Functor f => Sigma t -> (t ~> Case f a) -> f a
matchCases (Sigma t x) pi = ($x) <$> handleCase (pi t)
