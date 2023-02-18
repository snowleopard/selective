{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Selective.Trans.Except
-- Copyright  : (c) Andrey Mokhov 2018-2022
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- This is a library for /selective applicative functors/, or just
-- /selective functors/ for short, an abstraction between applicative functors
-- and monads, introduced in this paper:
-- https://www.staff.ncl.ac.uk/andrey.mokhov/selective-functors.pdf.
--
-- This module defines a newtype around 'ExceptT' from @transformers@ with less
-- restrictive 'Applicative', 'Selective', and 'Alternative' implementations.
-- It supplies an @instance 'Selective' f => 'Selective' ('ExceptT' e f)@, which
-- makes 'ExceptT' a bona-fide 'Selective' transformer.
--
-- The API follows the API from the @transformers@ package, so it can be used as
-- a drop-in replacement. The documentation can be found in the
-- [@transformers@](https://hackage.haskell.org/package/transformers/docs/Control-Monad-Trans-Except.html) package.
-----------------------------------------------------------------------------
module Control.Selective.Trans.Except where

import Control.Applicative (Alternative (empty, (<|>)))
import Control.Monad (MonadPlus)
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Zip (MonadZip)
import Data.Functor.Classes
import Data.Functor.Identity
#if MIN_VERSION_base(4,13,0)
-- MonadFail is imported already
#else
#if MIN_VERSION_base(4,9,0)
import Control.Monad.Fail
#endif
#endif
#if MIN_VERSION_base(4,12,0)
import Data.Functor.Contravariant (Contravariant)
#endif

import qualified Control.Monad.Trans.Except as T
import Control.Monad.Trans.Class

import Control.Selective
import Control.Monad.Signatures

-- | A newtype around 'T.ExceptT' from @transformers@.
newtype ExceptT e m a = ExceptT { unwrap :: T.ExceptT e m a }
  deriving
    ( Functor, Monad, MonadTrans, MonadFix, Foldable, Eq1, Ord1, Read1, Show1
    , MonadZip, MonadIO, MonadPlus, Eq, Ord, Read, Show
#if MIN_VERSION_base(4,9,0)
    , MonadFail
#endif
#if MIN_VERSION_base(4,12,0)
    , Contravariant
#endif
    )

instance Traversable f => Traversable (ExceptT e f) where
    traverse f (ExceptT efa) = ExceptT <$> traverse f efa

-- | No @'Monad' f@ constraint is needed. If the first argument to '<*>' results
-- in a @Left e@, the second argument is not executed.
instance Selective f => Applicative (ExceptT e f) where
    pure = ExceptT . T.ExceptT . pure . Right

    ExceptT (T.ExceptT f) <*> ExceptT (T.ExceptT a) =
        ExceptT $ T.ExceptT $ select (prepare <$> f) (combine <$> a)
      where
        prepare :: Either e (a -> b) -> Either (a -> b) (Either e b)
        prepare = either (Right . Left) Left

        combine :: Either e a -> (a -> b) -> Either e b
        combine = flip fmap

-- | No @'Monad' f@ constraint is needed.
instance Selective f => Selective (ExceptT e f) where
    select (ExceptT (T.ExceptT x)) (ExceptT (T.ExceptT f)) =
        ExceptT $ T.ExceptT $ select (prepare <$> x) (combine <$> f)
      where
        prepare :: Either e (Either a b) -> Either a (Either e b)
        prepare = either (Right . Left) (fmap Right)

        combine :: Either e (a -> b) -> a -> Either e b
        combine (Left e)  _ = Left e
        combine (Right f) a = Right (f a)

-- | No @'Monad' f@ constraint is needed.
instance (Selective f, Monoid e) => Alternative (ExceptT e f) where
    empty = ExceptT $ T.ExceptT $ pure $ Left mempty

    ExceptT (T.ExceptT x) <|> ExceptT (T.ExceptT y) =
        ExceptT $ T.ExceptT $ orElse x y

-- | Inject an 'T.ExceptT' value into the newtype wrapper.
wrap :: T.ExceptT e m a -> ExceptT e m a
wrap = ExceptT

type Except e = ExceptT e Identity

#if MIN_VERSION_transformers(0,5,6)
except :: Monad m => Either e a -> ExceptT e m a
#else
except :: Either e a -> Except e a
#endif
except = ExceptT . T.except

runExcept :: Except e a -> Either e a
runExcept = T.runExcept . unwrap

mapExcept :: (Either e a -> Either e' b) -> Except e a -> Except e' b
mapExcept f = ExceptT . T.mapExcept f . unwrap

withExcept :: (e -> e') -> Except e a -> Except e' a
withExcept f = ExceptT . T.withExcept f . unwrap

runExceptT :: ExceptT e m a -> m (Either e a)
runExceptT = T.runExceptT . unwrap

mapExceptT :: (m (Either e a) -> n (Either e' b)) -> ExceptT e m a -> ExceptT e' n b
mapExceptT f = ExceptT . T.mapExceptT f . unwrap

withExceptT :: Functor m => (e -> e') -> ExceptT e m a -> ExceptT e' m a
withExceptT f = ExceptT . T.withExceptT f . unwrap

throwE :: Monad m => e -> ExceptT e m a
throwE = ExceptT . T.throwE

catchE :: Monad m => ExceptT e m a -> (e -> ExceptT e' m a) -> ExceptT e' m a
catchE action continuation = ExceptT $ T.catchE (unwrap action) (unwrap . continuation)

liftCallCC :: CallCC m (Either e a) (Either e b) -> CallCC (ExceptT e m) a b
liftCallCC callCC caller = ExceptT $ T.liftCallCC callCC (unwrap . caller . (ExceptT .))

liftListen :: Monad m => Listen w m (Either e a) -> Listen w (ExceptT e m) a
liftListen listen (ExceptT action) = ExceptT $ T.liftListen listen action

liftPass :: Monad m => Pass w m (Either e a) -> Pass w (ExceptT e m) a
liftPass pass (ExceptT action) = ExceptT $ T.liftPass pass action
