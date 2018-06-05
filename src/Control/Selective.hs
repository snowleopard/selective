{-# LANGUAGE ConstraintKinds, DefaultSignatures, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Control.Selective (
    -- * Type class
    Selective (..), select, handleA, apS, handleM,

    -- * Conditional combinators
    ifS, whenS, fromMaybeS, whileS, (<||>), (<&&>), anyS, allS,

    -- * Static analysis
    oblivious, Task, dependencies
    ) where

import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Applicative
import Data.Functor.Identity
import Data.Proxy
import Data.Semigroup

import qualified Data.Set as Set

-- | Selective applicative functor. You can think of 'handle' as a selective
-- function application: you apply the function only when given a value of type
-- @Left a@. Otherwise, you skip it (along with all its effects) and return the
-- @b@ from @Right b@. Intuitively, 'handle' allows you to efficiently handle an
-- error, which we often represent by @Left a@ in Haskell.
--
-- Law: If fmap Left x /= fmap Right x then
--      * handle f (fmap Left  x) == f <*> x
--      * handle f (fmap Right x) == x
--
-- For example, when f = Maybe we have:
--    * handle f (Just (Left  a)) == f <*> x
--    * handle f (Just (Right b)) == x
--    * handle f Nothing is not constrained, allowing the implementation to
--      select between the two above behaviours. The default implementation
--      provided for a Monad f skips the effect, i.e. handle f Nothing = Nothing.
class Applicative f => Selective f where
    handle :: f (a -> b) -> f (Either a b) -> f b
    default handle :: Monad f => f (a -> b) -> f (Either a b) -> f b
    handle = handleM

-- | The 'select' function is a natural generalisation of 'handle': instead of
-- skipping unnecessary effects, it selects which of the two given effectful
-- functions to apply to a given argument. It is possible to implement 'select'
-- in terms of 'handle', which is a good puzzle (give it a try!).
select :: Selective f => f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
select l r = handle r . handle (fmap (fmap Right) l) . fmap (fmap Left)

-- | We can write a function with the type signature of 'handle' using the
-- 'Applicative' type class, but it will have different behaviour -- it will
--- always execute the effects associated with the handler, hence being less
-- efficient.
handleA :: Applicative f => f (a -> b) -> f (Either a b) -> f b
handleA f x = either <$> f <*> pure id <*> x

-- | 'Selective' is more powerful than 'Applicative': we can recover the
-- application operator '<*>'.
apS :: Selective f => f (a -> b) -> f a -> f b
apS f = handle f . fmap Left

-- | One can easily implement monadic 'handleM' with the right behaviour, hence
-- any 'Monad' is 'Selective'.
handleM :: Monad f => f (a -> b) -> f (Either a b) -> f b
handleM mf mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> pure b

-- Many useful Monad combinators that can be implemented with Selective

-- | Branch on a Boolean value, skipping unnecessary effects.
ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS i t f = select (fmap const f) (fmap const t) $
    fmap (\b -> if b then Right () else Left ()) i

-- | Conditionally apply an effect.
whenS :: Selective f => f Bool -> f () -> f ()
whenS x act = ifS x act (pure ())

-- | A lifted version of 'fromMaybe'.
fromMaybeS :: Selective f => f a -> f (Maybe a) -> f a
fromMaybeS x = handle (fmap const x) . fmap (maybe (Left ()) Right)

-- | Keep checking a given effectful condition while it holds.
whileS :: Selective f => f Bool -> f ()
whileS act = whenS act (whileS act)

-- | A lifted version of lazy Boolean OR.
(<||>) :: Selective f => f Bool -> f Bool -> f Bool
(<||>) a b = ifS a (pure True) b

-- | A lifted version of lazy Boolean AND.
(<&&>) :: Selective f => f Bool -> f Bool -> f Bool
(<&&>) a b = ifS a b (pure False)

-- | A lifted version of 'any'. Retains the short-circuiting behaviour.
anyS :: Selective f => (a -> f Bool) -> [a] -> f Bool
anyS p = foldr ((<||>) . p) (pure False)

-- | A lifted version of 'all'. Retains the short-circuiting behaviour.
allS :: Selective f => (a -> f Bool) -> [a] -> f Bool
allS p = foldr ((<&&>) . p) (pure True)

-- Instances

-- As a quick experiment, try: ifS (pure True) (print 1) (print 2)
instance Selective IO where

-- And... we need to write a lot more instances
instance Selective [] where
instance Selective ((->) a) where
instance Monoid a => Selective ((,) a) where
instance Selective Identity where
instance Selective Maybe where
instance Selective Proxy where

instance Monad m => Selective (ReaderT s m) where
instance Monad m => Selective (StateT s m) where
instance (Monoid s, Monad m) => Selective (WriterT s m) where

-- Selective instance for the standard Applicative Validation
-- This is a good example of a Selective functor which is not a Monad
data Validation e a = Failure e | Success a deriving Show

instance Functor (Validation e) where
    fmap _ (Failure e) = Failure e
    fmap f (Success a) = Success (f a)

instance Semigroup e => Applicative (Validation e) where
    pure = Success
    Failure e1 <*> Failure e2 = Failure (e1 <> e2)
    Failure e1 <*> Success _  = Failure e1
    Success _  <*> Failure e2 = Failure e2
    Success f  <*> Success a  = Success (f a)

instance Semigroup e => Selective (Validation e) where
    handle _ (Success (Right b)) = Success b
    handle f (Success (Left  a)) = f <*> Success a
    handle _ (Failure e        ) = Failure e

-- Static analysis of selective functors
newtype Illegal f a = Illegal { runIllegal :: f a } deriving (Applicative, Functor)

-- This instance is not legal but useful for static analysis: see 'dependencies'.
instance Applicative f => Selective (Illegal f) where
    handle = handleA

-- Run all effects of a given selective computation. Cannot be implemented using
-- a legal Selective instance.
oblivious :: Applicative f => (forall s. Selective s => s a) -> f a
oblivious = runIllegal

-- | The task abstraction, as described in
-- https://blogs.ncl.ac.uk/andreymokhov/the-task-abstraction/.
type Task c k v = forall f. c f => (k -> f v) -> k -> Maybe (f v)

-- | Extract dependencies from a selective task. Probably does something illegal
-- to the given task, but you'll never know ;)
dependencies :: Ord k => Task Selective k v -> k -> [k]
dependencies task key = case task (Illegal . Const . Set.singleton) key of
    Nothing -> []
    Just act -> Set.toList $ getConst $ runIllegal act
