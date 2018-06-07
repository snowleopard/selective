{-# LANGUAGE ConstraintKinds, DefaultSignatures, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Control.Selective (
    -- * Type class
    Selective (..), select, handleA, apS, handleM,

    -- * Conditional combinators
    ifS, whenS, fromMaybeS, whileS, (<||>), (<&&>), anyS, allS,

    -- * Static analysis
    Validation (..), Task, dependencies
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
-- function application: you apply a handler function only when given a value of
-- type @Left a@. Otherwise, you skip the function (along with all its effects)
-- and return the @b@ from @Right b@. Intuitively, 'handle' allows you to
-- efficiently handle errors that are often represented by @Left a@ in Haskell.
--
-- Note: the laws are still in flux. They still look unsatisfactory, so any ideas
-- on how to improve them yet keep Const and Validation instances are welcome!
--
-- Laws: 1) handle (Left <$> x) f == flip ($) <$> x <*> f
--       2) if Left <$> x /= Right <$> x then handle (Right <$> x) f == x
--
-- For example, when f = Maybe we have:
--       1) handle (Just (Left  x)) f == flip ($) <$> Just x <*> f
--          handle Nothing          f == Nothing
--       2) handle (Just (Right x)) f == Just x
class Applicative f => Selective f where
    handle :: f (Either a b) -> f (a -> b) -> f b
    default handle :: Monad f => f (Either a b) -> f (a -> b) -> f b
    handle = handleM

-- | An operator alias for 'handle'.
(<*?) :: Selective f => f (Either a b) -> f (a -> b) -> f b
(<*?) = handle

infixl 4 <*?

-- | The 'select' function is a natural generalisation of 'handle': instead of
-- skipping unnecessary effects, it selects which of the two given effectful
-- functions to apply to a given argument. It is possible to implement 'select'
-- in terms of 'handle', which is a good puzzle (give it a try!).
select :: Selective f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
select x l r = fmap (fmap Left) x <*? fmap (fmap Right) l <*? r

-- | We can write a function with the type signature of 'handle' using the
-- 'Applicative' type class, but it will have different behaviour -- it will
--- always execute the effects associated with the handler, hence being less
-- efficient.
handleA :: Applicative f => f (Either a b) -> f (a -> b) -> f b
handleA x f = fmap (\e f -> either f id e) x <*> f

-- | 'Selective' is more powerful than 'Applicative': we can recover the
-- application operator '<*>'.
apS :: Selective f => f (a -> b) -> f a -> f b
apS f x = fmap Left f <*? fmap (flip ($)) x

-- | One can easily implement monadic 'handleM' with the right behaviour, hence
-- any 'Monad' is 'Selective'.
handleM :: Monad f => f (Either a b) -> f (a -> b) -> f b
handleM mx mf = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> pure b

-- Many useful Monad combinators that can be implemented with Selective

-- | Branch on a Boolean value, skipping unnecessary effects.
ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS i t f = select (fmap (\b -> if b then Right () else Left ()) i)
    (fmap const f) (fmap const t)

-- | Conditionally apply an effect.
whenS :: Selective f => f Bool -> f () -> f ()
whenS x act = ifS x act (pure ())

-- | A lifted version of 'fromMaybe'.
fromMaybeS :: Selective f => f a -> f (Maybe a) -> f a
fromMaybeS dx x = handle (fmap (maybe (Left ()) Right) x) (fmap const dx)

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
    handle (Success (Right b)) _ = Success b
    handle (Success (Left  a)) f = flip ($) <$> Success a <*> f
    handle (Failure e        ) _ = Failure e

-- Static analysis of selective functors
instance Monoid m => Selective (Const m) where
    handle = handleA

-- | The task abstraction, as described in
-- https://blogs.ncl.ac.uk/andreymokhov/the-task-abstraction/.
type Task c k v = forall f. c f => (k -> f v) -> k -> Maybe (f v)

-- | Extract dependencies from a selective task.
dependencies :: Ord k => Task Selective k v -> k -> [k]
dependencies task key = case task (Const . Set.singleton) key of
    Nothing -> []
    Just act -> Set.toList $ getConst act
