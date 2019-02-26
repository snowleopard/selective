{-# LANGUAGE StandaloneDeriving, DerivingVia #-}
{-# LANGUAGE FlexibleInstances, TupleSections, ExplicitForAll, TypeApplications #-}

module Laws where

import Test.QuickCheck hiding (Failure, Success)
import Data.Bifunctor
import Data.Functor.Const
import Control.Selective
import Data.Functor.Identity
import Control.Monad.State
import Text.Show.Functions()

-- | TODO:
-- ifS (pure x) a1 b1 *> ifS (pure x) a2 b2 = ifS (pure x) (a1 *> a2) (b1 *> b2)

--------------------------------------------------------------------------------
------------------------ Laws --------------------------------------------------
--------------------------------------------------------------------------------
-- | Identity
lawIdentity :: (Selective f, Eq (f a)) => f (Either a a) -> Bool
lawIdentity x = (x <*? pure id) == (either id id <$> x)

-- | Distributivity
lawDistributivity :: (Selective f, Eq (f b)) => Either a b -> f (a -> b) -> f (a -> b) -> Bool
lawDistributivity x y z = (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))

-- | Associativity
lawAssociativity :: (Selective f, Eq (f c)) =>
        f (Either b c) -> f (Either a (b -> c)) -> f (a -> b -> c) -> Bool
lawAssociativity x y z = (x <*? (y <*? z)) == ((f <$> x) <*? (g <$> y) <*? (h <$> z))
        where
            f x = Right <$> x
            g y = \a -> bimap (,a) ($a) y
            h z = uncurry z

{- | If 'f' is a 'Monad' |-}

lawMonad :: (Selective f, Monad f, Eq (f b)) =>
            f (Either a b) -> f (a -> b) -> Bool
lawMonad x f = select x f == selectM x f

--------------------------------------------------------------------------------
------------------------ Theorems ----------------------------------------------
--------------------------------------------------------------------------------
{-| Theorems about selective applicative functors,
    as presented in the Fig.4 of the paper
|-}

-- | Apply a pure function to the result:
theorem1 :: (Selective f, Eq (f c)) =>
            (a -> c) -> f (Either b a) -> f (b -> a) -> Bool
theorem1 f x y = (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))

-- | Apply a pure function to the Left case of the first argument:
theorem2 :: (Selective f, Eq (f c)) =>
            (a -> b) -> f (Either a c) -> f (b -> c) -> Bool
theorem2 f x y = (select (first f <$> x) y) == (select x ((. f) <$> y))

-- | Apply a pure function to the second argument:
theorem3 :: (Selective f, Eq (f c)) =>
            (a -> b -> c) -> f (Either b c) -> f a -> Bool
theorem3 f x y = (select x (f <$> y)) == (select (first (flip f) <$> x) (flip ($) <$> y))

-- | Generalised identity:
theorem4 :: (Selective f, Eq (f b)) => f (Either a b) -> (a -> b) -> Bool
theorem4 x y = (x <*? pure y) == (either y id <$> x)

{-| For rigid selective functors (in particular, for monads):
|-}

-- | Selective apply
theorem5 :: (Selective f, Eq (f b)) => f (a -> b) -> f a -> Bool
theorem5 f g = (f <*> g) == (f `apS` g)

-- | Interchange
theorem6 :: (Selective f, Eq (f c)) =>
            f a -> f (Either b c) -> f (b -> c) -> Bool
theorem6 x y z = (x *> (y <*? z)) == ((x *> y) <*? z)

--------------------------------------------------------------------------------
------------------------ Properties ----------------------------------------------
--------------------------------------------------------------------------------

-- | pure-right
--   pure (Right x) <*? y = pure x
propertyPureRight :: (Selective f, Eq (f a)) => a -> f (b -> a) -> Bool
propertyPureRight x y = (pure (Right x) <*? y) == pure x

-- | pure-left
--   pure (Left x) <*? y = ($x) <$> y
propertyPureLeft :: (Selective f, Eq (f b)) => a -> f (a -> b) -> Bool
propertyPureLeft x y = (pure (Left x) <*? y) == (($x) <$> y)

--------------------------------------------------------------------------------
------------------------ Over --------------------------------------------------
--------------------------------------------------------------------------------
deriving instance Eq m => Eq (Over m a)
deriving via (Const m a) instance Arbitrary m => Arbitrary (Over m a)

propertyPureRightOver :: IO ()
propertyPureRightOver = quickCheck (propertyPureRight @(Over String) @Int)

--------------------------------------------------------------------------------
------------------------ Under -------------------------------------------------
--------------------------------------------------------------------------------
deriving instance Eq m => Eq (Under m a)
deriving via (Const m a) instance Arbitrary m => Arbitrary (Under m a)

propertyPureRightUnder :: IO ()
propertyPureRightUnder = quickCheck (propertyPureRight @(Under String) @Int)

--------------------------------------------------------------------------------
------------------------ Validation --------------------------------------------
--------------------------------------------------------------------------------
deriving instance (Eq e, Eq a) => Eq (Validation e a)

-- | This is a copy-paste of the 'Arbitrary2' instance for 'Either' defined in
--   the 'Test.QuickCheck.Arbitrary' module. 'Left' is renamed to 'Failure' and
--   'Right' to 'Success'.
instance Arbitrary2 Validation where
  liftArbitrary2 arbA arbB = oneof [liftM Failure arbA, liftM Success arbB]

  liftShrink2 shrA _ (Failure x)  = [ Failure  x' | x' <- shrA x ]
  liftShrink2 _ shrB (Success y) = [ Success y' | y' <- shrB y ]

instance (Arbitrary e, Arbitrary a) => Arbitrary (Validation e a) where
  arbitrary = arbitrary2
  shrink = shrink2

--------------------------------------------------------------------------------
------------------------ Maybe -------------------------------------------------
--------------------------------------------------------------------------------

propertyPureRightMaybe :: IO ()
propertyPureRightMaybe = quickCheck (propertyPureRight @Maybe @Int @Int)

--------------------------------------------------------------------------------
------------------------ Identity ----------------------------------------------
--------------------------------------------------------------------------------

propertyPureRightIdentity :: IO ()
propertyPureRightIdentity = quickCheck (propertyPureRight @Identity @Int @Int)
