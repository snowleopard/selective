{-# LANGUAGE ConstraintKinds, DefaultSignatures, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Control.Selective (
    -- * Type class
    Selective (..), apS, handleA, selectA, handleM, selectM,

    -- * Conditional combinators
    ifS, whenS, fromMaybeS, whileS, (<||>), (<&&>), anyS, allS,

    -- * Static analysis
    oblivious, Task, dependencies
    ) where

import Control.Monad.Trans.State
import Control.Applicative
import Data.Functor.Compose

import qualified Data.Set as Set

-- Selective applicative functor.
--
-- Laws: 1) handle f (fmap Left  x) == f <*> x  (free theorem)
--       2) handle f (fmap Right x) == x
--
class Applicative f => Selective f where
    handle :: f (a -> b) -> f (Either a b) -> f b
    default handle :: Monad f => f (a -> b) -> f (Either a b) -> f b
    handle = handleM

-- The 'select' function is a natural generalisation of 'handle': instead of
-- skipping unnecessary effects, it selects which of the two given effectful
-- functions to apply to a given argument.
select :: Selective f => f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
select l r = handle r . handle (fmap (fmap Right) l) . fmap (fmap Left)

-- We can recover <*> from 'handle'
apS :: Selective f => f (a -> b) -> f a -> f b
apS f = handle f . fmap Left

-- This is the only possible implementation of 'handle' using Applicative
-- It always performs f's effects
handleA :: Applicative f => f (a -> b) -> f (Either a b) -> f b
handleA f x = either <$> f <*> pure id <*> x

selectA :: Applicative f => f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
selectA f g x = either <$> f <*> g <*> x

-- Any Monad is Selective
handleM :: Monad f => f (a -> b) -> f (Either a b) -> f b
handleM mf mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> pure b

selectM :: Monad f => f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
selectM mf mg mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> fmap ($b) mg

-- Many useful Monad combinators that can be implemented with Selective

ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS i t f = select (fmap const f) (fmap const t) $
    fmap (\b -> if b then Right () else Left ()) i

whenS :: Selective f => f Bool -> f () -> f ()
whenS x act = ifS x act (pure ())

fromMaybeS :: Selective f => f a -> f (Maybe a) -> f a
fromMaybeS x = handle (fmap const x) . fmap (maybe (Left ()) Right)

whileS :: Selective f => f Bool -> f ()
whileS act = whenS act (whileS act)

(<||>) :: Selective f => f Bool -> f Bool -> f Bool
(<||>) a b = ifS a (pure True) b

(<&&>) :: Selective f => f Bool -> f Bool -> f Bool
(<&&>) a b = ifS a b (pure False)

anyS :: Selective f => (a -> f Bool) -> [a] -> f Bool
anyS p = foldr ((<||>) . p) (pure False)

allS :: Selective f => (a -> f Bool) -> [a] -> f Bool
allS p = foldr ((<&&>) . p) (pure True)

-- Instances

-- Do Selective functors compose?
-- The implementation below is not lawful:
--
--   handle (Compose Nothing) (Compose (Just (Just (Right 8)))) == Nothing
--
-- That is, the first layer of effects is still applied.
instance (Selective f, Selective g) => Selective (Compose f g) where
    handle (Compose f) (Compose x) = Compose $ pure handle <*> f <*> x

-- Try: ite (pure True) (print 1) (print 2)
instance Selective IO where

instance Monad m => Selective (StateT s m) where

-- Static analysis of selective functors
newtype Illegal f a = Illegal { runIllegal :: f a } deriving (Applicative, Functor)

-- This instance is not legal but useful for static analysis: see 'dependencies'.
instance Applicative f => Selective (Illegal f) where
    handle = handleA

-- Run all effects of a given selective computation. Cannot be implemented using
-- a legal Selective instance.
oblivious :: Applicative f => (forall s. Selective s => s a) -> f a
oblivious = runIllegal

-- See https://blogs.ncl.ac.uk/andreymokhov/the-task-abstraction/
type Task c k v = forall f. c f => (k -> f v) -> k -> Maybe (f v)

-- Extract dependencies from a selective task
dependencies :: Ord k => Task Selective k v -> k -> [k]
dependencies task key = case task (Illegal . Const . Set.singleton) key of
    Nothing -> []
    Just act -> Set.toList $ getConst $ runIllegal act
