{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{- |
FIXME some inspiration/guidance needed here
-}
module Control.Selective.Trans.Validation where

import Data.Functor.Compose
#if MIN_VERSION_base(4,12,0)
#endif

import Control.Monad.Trans.Class

import Control.Selective

-- | A newtype around @transformers@' 'Transformers.ValidationT'.
newtype ValidationT e m a = ValidationT
    { runValidationT :: m (Validation e a) }
    deriving
        ( Functor, Foldable, Traversable
        )


-- TODO
#if MIN_VERSION_base(4,12,0)
        --, Contravariant
#endif

-- Eq1, Ord1, Read1, Show1,
--, Eq, Ord, Read, Show

#if MIN_VERSION_base(4,9,0)
--        , MonadFail
#endif
-- MonadZip, MonadIO, MonadPlus, -- alternative versions?
-- Monad, MonadTrans, MonadFix,

instance MonadTrans (ValidationT e) where
    lift = ValidationT . fmap Success

deriving via Compose f (Validation e) instance (Applicative f, Semigroup e) => Applicative (ValidationT e f)

-- TODO want:
-- deriving via ComposeTraversable
-- See https://github.com/snowleopard/selective/pull/52/
instance (Selective f, Semigroup e) => Selective (ValidationT e f) where
    select eab fab = ValidationT $ select (sequenceA <$> runValidationT eab) (sequenceA <$> runValidationT fab)

-- TODO reproduce API of Validation
