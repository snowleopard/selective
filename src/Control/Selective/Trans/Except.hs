{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, DeriveTraversable, DerivingVia #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Selective.Trans.Except
-- Copyright  : (c) Andrey Mokhov 2018-2024
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- This is a library for /selective applicative functors/, or just
-- /selective functors/ for short, an abstraction between applicative functors
-- and monads, introduced in this paper: https://dl.acm.org/doi/10.1145/3341694.
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

import Control.Selective
import Control.Monad.Signatures

-- | A newtype wrapper around 'T.ExceptT' from @transformers@ that provides less
-- restrictive 'Applicative', 'Selective' and 'Alternative' instances.
newtype ExceptT e f a = ExceptT { unwrap :: T.ExceptT e f a }
  deriving stock (Functor, Foldable, Traversable, Eq, Ord, Read, Show)
  deriving newtype
    (Monad, Contravariant, MonadFix, MonadFail, MonadZip, MonadIO, MonadPlus
    , Eq1, Ord1, Read1, Show1 ) -- These require -Wno-redundant-constraints
  deriving (Applicative, Selective, Alternative) via (ComposeEither f e)

{- Why don't we provide a `MonadTrans (ExceptT e)` instance?

   Recall the definition of the MonadTrans type class:

     class (forall m. Monad m => Monad (t m)) => MonadTrans t where
         lift :: Monad m => m a -> t m a

   If we instantiate `t` to `ExceptT e` in the constraint, we get

     forall m. Monad m => Monad (ExceptT e m)

   but the `Applicative (ExceptT e m)` instance comes with the `Selective m`
   constraint, and since Selective is not a superclass of Monad, we're stuck.
   In other words, `ExceptT` is really not a universal monad transformer: it
   works only for monads `m` that also happen to have a `Selective m` instance.

   I can see three possible solutions but none of them has a chance of working
   in practice:

     * Change the constraint in the definition of MonadTrans to

         forall m. (Selective m, Monad m) => Monad (ExceptT e m)

     * Make Selective a superclass of Monad
     * Revert the "Applicative is a superclass of Monad" proposal (lol!)

   And so we just don't provide `MonadTrans (ExceptT e)` instance.

   We could provide a SelectiveTrans instance instead, where

     class (forall f. Selective f => Selective (t f)) => SelectiveTrans t where
         lift :: Selective f => f a -> t f a

   Sounds fun!
-}

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
