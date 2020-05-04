{-# LANGUAGE DeriveFunctor, EmptyCase, TypeFamilies, GADTs, RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables, LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Batch
-- Copyright  : (c) Andrey Mokhov 2018-2020
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- An experiment in expressing Functor, Applicative and Monad using the Batch
-- type class.
-----------------------------------------------------------------------------
module Control.Batch where

import Data.Kind
import Prelude hiding (pure)

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

-- | A potentially uncountable collection of tags for the same unit @()@ payload.
data Many a b where
    Many :: a -> Many a ()

class Functor f => Batch f where
    type Tag f :: (* -> *) -> Constraint
    batch :: Tag f t => ((forall x. t x -> x) -> a) -> (forall x. t x -> f x) -> f a

pure :: (Batch f, Tag f Zero) => a -> f a
pure a = batch (const a) (\(x :: Zero a) -> case x of {})

fmap :: (Batch f, Tag f (One a)) => (a -> b) -> f a -> f b
fmap f x = batch (\lookup -> f (lookup One)) (\One -> x)

mult :: (Batch f, Tag f (Two a b)) => f a -> f b -> f (a, b)
mult x y = batch (\lookup -> (lookup A, lookup B)) $ \case { A -> x; B -> y }

-- What about Many?
