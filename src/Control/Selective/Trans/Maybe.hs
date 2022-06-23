{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{- | A newtype around @transformers@ 'MaybeT' with less restrictive 'Applicative', 'Selective', and 'Alternative' implementations.

Supplies an @instance 'Selective' f => 'Selective' ('MaybeT' e f)@.
In other words, 'MaybeT' is a bona-fide 'Selective' transformer.

This tries to copy verbatim the API from @transformers@,
so it can be used as a drop-in replacement.
The documentation can be found in the [@transformers@](https://hackage.haskell.org/package/transformers/docs/Control-Monad-Trans-Maybe.html) package.
-}
module Control.Selective.Trans.Maybe where

import Control.Applicative (Alternative (empty, (<|>)))
import Control.Monad (MonadPlus)
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Zip (MonadZip)
import Data.Functor.Classes
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

import qualified Control.Monad.Trans.Maybe as Transformers
import Control.Monad.Trans.Class

import Control.Selective
import Control.Monad.Signatures
import Control.Selective.Trans.Except (ExceptT)
import qualified Control.Selective.Trans.Except as SelectiveExcept

-- | A newtype around @transformers@' 'Transformers.MaybeT'.
newtype MaybeT m a = MaybeT
    { toTransformers :: Transformers.MaybeT m a }
    deriving
        ( Functor, Monad, MonadTrans, MonadFix, Foldable, Eq1, Ord1, Read1, Show1, MonadZip, MonadIO, MonadPlus, Eq, Ord, Read, Show
#if MIN_VERSION_base(4,9,0)
        , MonadFail
#endif
#if MIN_VERSION_base(4,12,0)
        , Contravariant
#endif
        )

instance Traversable f => Traversable (MaybeT f) where
    traverse f (MaybeT efa)= MaybeT <$> traverse f efa

-- | No @'Monad' f@ constraint is needed.
--   If the first argument to '<*>' results in `Left e`,
--   the second argument is not executed.
instance Selective f => Applicative (MaybeT f) where
    pure = MaybeT . Transformers.MaybeT . pure . pure
    MaybeT (Transformers.MaybeT f) <*> MaybeT (Transformers.MaybeT m) = MaybeT $ Transformers.MaybeT
      $ maybe (Right Nothing) Left <$> f
      <*? (flip fmap <$> m)

-- | No @'Monad' f@ constraint is needed.
deriving via ComposeTraversable f Maybe instance Selective f => Selective (MaybeT f)

-- | No @'Monad' f@ constraint is needed.
instance Selective f => Alternative (MaybeT f) where
    empty = MaybeT $ Transformers.MaybeT $ pure Nothing
    MaybeT (Transformers.MaybeT mx) <|> MaybeT (Transformers.MaybeT my)
        = MaybeT $ Transformers.MaybeT
        $ Right <$> mx
        <*? (const <$> my)

-- | Convert back to the newtype.
fromTransformers :: Transformers.MaybeT m a -> MaybeT m a
fromTransformers = MaybeT

runMaybeT :: MaybeT m a -> m (Maybe a)
runMaybeT = Transformers.runMaybeT . toTransformers

mapMaybeT :: (m (Maybe a) -> n (Maybe b)) -> MaybeT m a -> MaybeT n b
mapMaybeT f = MaybeT . Transformers.mapMaybeT f . toTransformers

#if MIN_VERSION_transformers(0,6,0)
hoistMaybe :: Applicative m => Maybe b -> MaybeT m b
hoistMaybe = fromTransformers . Transformers.hoistMaybe
#endif

maybeToExceptT :: Functor m => e -> MaybeT m a -> ExceptT e m a
maybeToExceptT e = SelectiveExcept.fromTransformers . Transformers.maybeToExceptT e . toTransformers

exceptToMaybeT :: Functor m => ExceptT e m a -> MaybeT m a
exceptToMaybeT = fromTransformers . Transformers.exceptToMaybeT . SelectiveExcept.toTransformers


liftCallCC :: CallCC m (Maybe a) (Maybe b) -> CallCC (MaybeT m) a b
liftCallCC callCC caller = MaybeT $ Transformers.liftCallCC callCC (toTransformers . caller . (MaybeT .))

liftCatch :: Catch e m (Maybe a) -> Catch e (MaybeT m) a
liftCatch f m h = MaybeT $ Transformers.liftCatch f (toTransformers m) (toTransformers . h)

liftListen :: Monad m => Listen w m (Maybe a) -> Listen w (MaybeT m) a
liftListen listen (MaybeT action) = MaybeT $ Transformers.liftListen listen action

liftPass :: Monad m => Pass w m (Maybe a) -> Pass w (MaybeT m) a
liftPass pass (MaybeT action) = MaybeT $ Transformers.liftPass pass action
