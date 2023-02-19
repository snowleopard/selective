{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, DeriveTraversable, DerivingVia #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Selective.Trans.Except
-- Copyright  : (c) Andrey Mokhov 2018-2023
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

import Control.Applicative (Alternative)
import Control.Monad (MonadPlus)
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Zip (MonadZip)
import Data.Functor.Classes
import Data.Functor.Contravariant (Contravariant)
import Data.Functor.Identity
#if MIN_VERSION_base(4,13,0)
-- MonadFail is imported already
#else
import Control.Monad.Fail
#endif

import qualified Control.Monad.Trans.Except as T
import Control.Monad.Trans.Class

import Control.Selective
import Control.Monad.Signatures

-- | A newtype wrapper around 'T.ExceptT' from @transformers@ that provides less
-- restrictive 'Applicative', 'Selective' and 'Alternative' instances.
newtype ExceptT e f a = ExceptT { unwrap :: T.ExceptT e f a }
  deriving
    ( Functor, Foldable, Traversable, Monad, Contravariant, Eq, Ord, Read, Show
    , MonadTrans, MonadFix, MonadFail, MonadZip, MonadIO, MonadPlus, Eq1, Ord1
    , Read1, Show1 )
  deriving (Applicative, Selective, Alternative) via (ComposeEither f e)

-- | Inject an 'T.ExceptT' value into the newtype wrapper.
wrap :: T.ExceptT e m a -> ExceptT e m a
wrap = ExceptT

type Except e = ExceptT e Identity

except :: Monad m => Either e a -> ExceptT e m a
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
