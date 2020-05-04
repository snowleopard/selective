{-# LANGUAGE DeriveFunctor, TypeFamilies, GADTs, RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables, LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Match.Arrow
-- Copyright  : (c) Andrey Mokhov 2018-2020
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- An experiment in expressing arrows using the Match type class.
-----------------------------------------------------------------------------
module Control.Match.Arrow where

import Control.Category
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

-- | A type class that allows lifting 'matchPure' into an arrow 'a'.
class Category a => Match a where
    type Tag a :: (* -> *) -> Constraint
    arr   :: (i -> o) -> a i o
    match :: Tag a t => a i (Sigma t) -> (forall x. t x -> a x o) -> a i o

-- Interestingly, this matches the type Mono from this blog post:
-- https://elvishjerricco.github.io/2017/03/23/applicative-sorting.html
data ManyT a b c where
    ManyT :: a -> ManyT a b b

-- This seems unsatisfactory
first :: (Match a, Tag a (ManyT x i)) => a i o -> a (i, x) (o, x)
first a = match (arr $ \(i, x) -> Sigma (ManyT x) i) $
    \case ManyT x -> arr (\o -> (o, x)) . a

left :: (Match a, Tag a (Two i x)) => a i o -> a (Either i x) (Either o x)
left a = match (arr eitherToSigma) $ \case
    A -> arr Left . a
    B -> arr Right

right :: (Match a, Tag a (Two x i)) => a i o -> a (Either x i) (Either x o)
right a = match (arr eitherToSigma) $ \case
    A -> arr Left
    B -> arr Right . a

(|||) :: (Match a, Tag a (Two i1 i2)) => a i1 o1 -> a i2 o2 -> a (Either i1 i2) (Either o1 o2)
(|||) a b = match (arr eitherToSigma) $ \case
    A -> arr Left . a
    B -> arr Right . b

app :: (Match a, Tag a (ManyT (a i o) i)) => a (a i o, i) o
app = match (arr $ \(a, i) -> Sigma (ManyT a) i) $ \case ManyT x -> x
