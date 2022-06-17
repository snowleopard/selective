{-# LANGUAGE FlexibleInstances, TupleSections, TypeApplications #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Laws where

import Control.Arrow hiding (first, second)
import qualified Control.Monad.Trans.Except as Transformers
import Control.Monad.Trans.Writer
import Control.Selective
import Control.Selective.Trans.Except
import Data.Bifunctor (bimap, first, second)
import Data.Function
import Data.Functor.Identity
import Test.QuickCheck hiding (Failure, Success)
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
lawAssociativity x y z =
    (x <*? (y <*? z)) == ((f <$> x) <*? (g <$> y) <*? (h <$> z))
  where
    f     = fmap Right
    g y a = bimap (,a) ($a) y
    h     = uncurry

{- | If 'f' is a 'Monad' |-}

lawMonad :: (Selective f, Monad f, Eq (f b)) => f (Either a b) -> f (a -> b) -> Bool
lawMonad x f = select x f == selectM x f

selectALaw :: (Selective f, Eq (f b)) => f (Either a b) -> f (a -> b) -> Bool
selectALaw x f = select x f == selectA x f

--------------------------------------------------------------------------------
------------------------ Theorems ----------------------------------------------
--------------------------------------------------------------------------------
{-| Theorems about selective applicative functors, see Fig. 4 of the paper |-}

-- | Apply a pure function to the result:
theorem1 :: (Selective f, Eq (f c)) => (a -> c) -> f (Either b a) -> f (b -> a) -> Bool
theorem1 f x y = (f <$> select x y) == select (second f <$> x) ((f .) <$> y)

-- | Apply a pure function to the Left case of the first argument:
theorem2 :: (Selective f, Eq (f c)) => (a -> b) -> f (Either a c) -> f (b -> c) -> Bool
theorem2 f x y = select (first f <$> x) y == select x ((. f) <$> y)

-- | Apply a pure function to the second argument:
theorem3 :: (Selective f, Eq (f c)) => (a -> b -> c) -> f (Either b c) -> f a -> Bool
theorem3 f x y = select x (f <$> y) == select (first (flip f) <$> x) ((&) <$> y)

-- | Generalised identity:
theorem4 :: (Selective f, Eq (f b)) => f (Either a b) -> (a -> b) -> Bool
theorem4 x y = (x <*? pure y) == (either y id <$> x)

{-| For rigid selective functors (in particular, for monads) |-}

-- | Selective apply
theorem5 :: (Selective f, Eq (f b)) => f (a -> b) -> f a -> Bool
theorem5 f g = (f <*> g) == (f `apS` g)

-- | Interchange
theorem6 :: (Selective f, Eq (f c)) => f a -> f (Either b c) -> f (b -> c) -> Bool
theorem6 x y z = (x *> (y <*? z)) == ((x *> y) <*? z)

--------------------------------------------------------------------------------
------------------------ Properties ----------------------------------------------
--------------------------------------------------------------------------------

-- | Pure-Right: pure (Right x) <*? y = pure x
propertyPureRight :: (Selective f, Eq (f a)) => a -> f (b -> a) -> Bool
propertyPureRight x y = (pure (Right x) <*? y) == pure x

-- | Pure-Left: pure (Left x) <*? y = ($x) <$> y
propertyPureLeft :: (Selective f, Eq (f b)) => a -> f (a -> b) -> Bool
propertyPureLeft x y = (pure (Left x) <*? y) == (($x) <$> y)

--------------------------------------------------------------------------------
------------------------ Over --------------------------------------------------
--------------------------------------------------------------------------------
instance Arbitrary a => Arbitrary (Over a b) where
    arbitrary = Over <$> arbitrary
    shrink    = map Over . shrink . getOver

propertyPureRightOver :: IO ()
propertyPureRightOver = quickCheck (propertyPureRight @(Over String) @Int)

--------------------------------------------------------------------------------
------------------------ Under -------------------------------------------------
--------------------------------------------------------------------------------
instance Arbitrary a => Arbitrary (Under a b) where
    arbitrary = Under <$> arbitrary
    shrink    = map Under . shrink . getUnder

propertyPureRightUnder :: IO ()
propertyPureRightUnder = quickCheck (propertyPureRight @(Under String) @Int)

--------------------------------------------------------------------------------
------------------------ Validation --------------------------------------------
--------------------------------------------------------------------------------
instance (Arbitrary e, Arbitrary a) => Arbitrary (Validation e a) where
    arbitrary = oneof [Failure <$> arbitrary, Success <$> arbitrary]
    shrink (Failure x) = [ Failure x' | x' <- shrink x ]
    shrink (Success y) = [ Success y' | y' <- shrink y ]

--------------------------------------------------------------------------------
------------------------ ArrowMonad --------------------------------------------
--------------------------------------------------------------------------------
instance Eq a => Eq (ArrowMonad (->) a) where
    ArrowMonad f == ArrowMonad g = f () == g ()

instance Arbitrary a => Arbitrary (ArrowMonad (->) a) where
    arbitrary = ArrowMonad . const <$> arbitrary

instance Show a => Show (ArrowMonad (->) a) where
    show (ArrowMonad f) = show (f ())
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


--------------------------------------------------------------------------------
------------------------ Writer ------------------------------------------------
--------------------------------------------------------------------------------

instance (Arbitrary w, Arbitrary a) => Arbitrary (Writer w a) where
    arbitrary = curry writer <$> arbitrary <*> arbitrary

deriving instance (Arbitrary e, Arbitrary a) => Arbitrary (Transformers.Except e a)
deriving instance (Arbitrary e, Arbitrary a) => Arbitrary (Except e a)
