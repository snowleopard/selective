{-# LANGUAGE ConstraintKinds, DefaultSignatures, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Control.Selective (
    -- * Type class
    Selective (..), (<*?), select, handleA, apS, handleM,

    -- * Conditional combinators
    ifS, whenS, fromMaybeS, whileS, (<||>), (<&&>), anyS, allS,

    -- * Static analysis
    Validation (..), Task, dependencies
    ) where

import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Applicative
import Data.Bool
import Data.Functor.Identity
import Data.Proxy
import Data.Semigroup

import qualified Data.Set as Set

-- | Selective applicative functors. You can think of 'handle' as a selective
-- function application: you apply a handler function only when given a value of
-- type @Left a@. Otherwise, you can skip the function and associted effects
-- and return the @b@ from @Right b@. Intuitively, 'handle' allows you to
-- efficiently handle errors that are often represented by @Left a@ in Haskell.
--
-- The type signature of 'handle' is reminiscent of both '<*>' and '>>=', and
-- indeed a selective functor is in some sense a composition of an applicative
-- functor and the 'Either' monad.
--
-- Laws: (F1) Apply a pure function to the result:
--
--            f <$> handle x y = handle (second f <$> x) ((f .) <$> y)
--
--       (F2) Apply a pure function to the left (error) branch:
--
--            handle (first f <$> x) y = handle x ((. f) <$> y)
--
--       (F3) Apply a pure function to the handler:
--
--            handle x (f <$> y) = handle (first (flip f) <$> x) (flip ($) <$> y)
--
--       (P1) Apply a pure handler:
--
--            handle x (pure y) = either y id <$> x
--
--       (P2) Handle a pure error:
--
--            handle (pure (Left x)) y = ($x) <$> y
--
--       (A1) Associativity:
--
--            handle x (handle y z) = handle (handle (f <$> x) (g <$> y)) (h <$> z)
--
--            or in operator form:
--
--            x <*? (y <*? z) = (f <$> x) <*? (g <$> y) <*? (h <$> z)
--
--            where f x = Right <$> x
--                  g y = \a -> bimap (,a) ($a) y
--                  h z = uncurry z
--
--
--       Note there is no law for handling a pure value, i.e. we do not require
--       that the following holds:
--
--            handle (pure (Right x)) y = pure x
--
--       In particular, the following is allowed too:
--
--            handle (pure (Right x)) y = const x <$> y
--
--       We therefore allow 'handle' to be selective about effects in this case.
--
-- A consequence of the above laws is that 'apS' satisfies 'Applicative' laws.
-- We choose not to require that 'apS' = '<*>', since this forbids some
-- interesting instances, such as 'Validation'.
--
-- If f is also a 'Monad', we require that 'handle' = 'handleM'.
--
-- We can rewrite any selective expression in the following canonical form:
--
--          f (a + ... + z)    -- A value to be handled (+ denotes a sum type)
--       -> f (a -> (b + ...)) -- How to handle a's
--       -> f (b -> (c + ...)) -- How to handle b's
--       ...
--       -> f (y -> z)         -- How to handle y's
--       -> f z                -- The resulting z
--
-- See "Control.Selective.Sketch" for proof sketches.
class Applicative f => Selective f where
    handle :: f (Either a b) -> f (a -> b) -> f b
    default handle :: Monad f => f (Either a b) -> f (a -> b) -> f b
    handle = handleM

-- | An operator alias for 'handle', which is sometimes convenient. It tries to
-- follow the notational convention for 'Applicative' operators. The angle
-- bracket pointing to the left means we always use the corresponding value.
-- The value on the right, however, can be skipped, hence the question mark.
(<*?) :: Selective f => f (Either a b) -> f (a -> b) -> f b
(<*?) = handle

infixl 4 <*?

-- | The 'select' function is a natural generalisation of 'handle': instead of
-- skipping an unnecessary effect, it selects which of the two given effectful
-- functions to apply to a given argument. It is possible to implement 'select'
-- in terms of 'handle', which is a good puzzle (give it a try!).
select :: Selective f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
select x l r = fmap (fmap Left) x <*? fmap (fmap Right) l <*? r

-- | We can write a function with the type signature of 'handle' using the
-- 'Applicative' type class, but it will always execute the effects associated
-- with the handler, hence being potentially less efficient.
handleA :: Applicative f => f (Either a b) -> f (a -> b) -> f b
handleA x f = (\e f -> either f id e) <$> x <*> f

-- | 'Selective' is more powerful than 'Applicative': we can recover the
-- application operator '<*>'. In particular, the following 'Applicative' laws
-- hold when expressed using 'apS':
--
-- * Identity     : pure id <*> v = v
-- * Homomorphism : pure f <*> pure x = pure (f x)
-- * Interchange  : u <*> pure y = pure ($y) <*> u
-- * Composition  : (.) <$> u <*> v <*> w = u <*> (v <*> w)
apS :: Selective f => f (a -> b) -> f a -> f b
apS f x = handle (Left <$> f) (flip ($) <$> x)

-- | One can easily implement a monadic 'handleM' that satisfies the laws,
-- hence any 'Monad' is 'Selective'.
handleM :: Monad f => f (Either a b) -> f (a -> b) -> f b
handleM mx mf = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> pure b

-- Many useful 'Monad' combinators can be implemented with 'Selective'

-- | Branch on a Boolean value, skipping unnecessary effects.
ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS i t e = select (bool (Right ()) (Left ()) <$> i) (const <$> t) (const <$> e)

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
