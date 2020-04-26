{-# LANGUAGE DeriveFunctor, TypeFamilies, GADTs, RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables, LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Match.Profunctor
-- Copyright  : (c) Andrey Mokhov 2018-2020
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- An experiment in expressing profunctors using the Match type class.
-----------------------------------------------------------------------------
module Control.Match.Profunctor where

import Data.Kind
import Prelude hiding (id, (.))

-- | A generalised sum type where @t@ stands for the type of constructor "tags".
-- Each tag has a type parameter @x@ which determines the type of the payload.
-- A 'Sigma' @t@ value therefore contains a payload whose type is not visible
-- externally but is revealed when pattern-matching on the tag.
--
-- See 'Two', 'eitherToSigma' and 'sigmaToEither' for an example.
data Sigma t where
    Sigma :: t x -> x -> Sigma t

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
    Left  a -> Sigma A a
    Right b -> Sigma B b

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

-- | Hide the type of the payload a tag.
--
-- There is a whole library dedicated to this nice little GADT:
-- http://hackage.haskell.org/package/some.
data Some t where
    Some :: t a -> Some t

-- | A class of tags with no constraint.
class Unconstrained (t :: * -> *) where

instance Unconstrained Zero where
instance Unconstrained (One a) where
instance Unconstrained (Two a b) where
instance Unconstrained (Many a) where

-- | A class of tags that can be enumerated.
--
-- A valid instance must list every tag in the resulting list exactly once.
class Unconstrained t => Countable t where
    enumerate :: [Some t]

instance Countable Zero where
    enumerate = []

instance Countable (One a) where
    enumerate = [Some single]

instance Countable (Two a b) where
    enumerate = [Some A, Some B]

-- | Like 'Countable' but the list has finite length.
class Countable t => Finite t where

instance Finite Zero where
instance Finite (One a) where
instance Finite (Two a b) where

-- | Like 'Finite' but the list has length equal to one, so @enumerate@ must be
-- equal to @[Some single]@.
class Finite t => Single t where
    type Payload t
    single :: t (Payload t)
    matchSingle :: Sigma t -> Payload t

instance Single (One a) where
    type Payload (One a) = a
    single = One
    matchSingle (Sigma One x) = x

-- | Generalised pattern matching on a Sigma type using a Pi type to describe
-- how to handle each case.
matchPure :: Sigma t -> (forall x. t x -> x -> a) -> a
matchPure (Sigma t x) pi = pi t x


class Profunctor p where
    dimap :: (a -> b) -> (c -> d) -> p b c -> p a d

    lmap :: (a -> b) -> p b c -> p a c
    lmap f = dimap f Prelude.id

    rmap :: (b -> c) -> p a b -> p a c
    rmap = dimap Prelude.id

-- | A type class that allows lifting 'matchPure' into a profunctor 'p'.
class Profunctor p => Match p where
    type Tag p :: (* -> *) -> Constraint
    id    :: p a a
    match :: Tag p t => p a (Sigma t) -> (forall x. t x -> p x b) -> p a b

-- We have a category
arr :: Match p => (a -> b) -> p a b
arr f = rmap f id

(.) :: (Match p, Tag p (One b)) => p b c -> p a b -> p a c
(.) x y = match (rmap (Sigma One) y) $ \case One -> x

data ManyT a b c where
    ManyT :: a -> ManyT a b b

-- This seems unsatisfactory
first :: (Match p, Tag p (One b), Tag p (ManyT x a)) => p a b -> p (a, x) (b, x)
first p = match (arr $ \(a, x) -> Sigma (ManyT x) a) $
    \case ManyT x -> arr (\b -> (b, x)) . p

left :: (Match p, Tag p (One b), Tag p (Two a x)) => p a b -> p (Either a x) (Either b x)
left p = match (arr eitherToSigma) $ \case
    A -> arr Left . p
    B -> arr Right

right :: (Match p, Tag p (One b), Tag p (Two x a)) => p a b -> p (Either x a) (Either x b)
right p = match (arr eitherToSigma) $ \case
    A -> arr Left
    B -> arr Right . p
