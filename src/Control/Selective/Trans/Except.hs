{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- | A newtype around @transformers@ 'ExceptT' with less restrictive 'Applicative', 'Selective', and 'Alternative' implementations.

Supplies an @instance 'Selective' f => 'Selective' ('ExceptT' e f)@.
In other words, 'ExceptT' is a bona-fide 'Selective' transformer.

This tries to copy verbatim the API from @transformers@,
so it can be used as a drop-in replacement.
The documentation can be found in the [@transformers@](https://hackage.haskell.org/package/transformers/docs/Control-Monad-Trans-Except.html) package.
-}
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

import qualified Control.Monad.Trans.Except as Transformers
import Control.Monad.Trans.Class

import Control.Selective
import Control.Monad.Signatures

-- | A newtype around @transformers@' 'Transformers.ExceptT'.
newtype ExceptT e m a = ExceptT
    { toTransformers :: Transformers.ExceptT e m a }
    deriving
        ( Functor, Monad, MonadTrans, MonadFix, Foldable, Eq1, Ord1, Read1, Show1, MonadZip, MonadIO, MonadPlus, Eq, Ord, Read, Show
#if MIN_VERSION_base(4,9,0)
        , MonadFail
#endif
#if MIN_VERSION_base(4,12,0)
        , Contravariant
#endif
        )

instance Traversable f => Traversable (ExceptT e f) where
    traverse f (ExceptT efa)= ExceptT <$> traverse f efa

-- | No @'Monad' f@ constraint is needed.
--   If the first argument to '<*>' results in `Left e`,
--   the second argument is not executed.
instance Selective f => Applicative (ExceptT e f) where
    pure = ExceptT . Transformers.ExceptT . pure . pure
    ExceptT (Transformers.ExceptT f) <*> ExceptT (Transformers.ExceptT m) = ExceptT $ Transformers.ExceptT
      $ either (Right . Left) Left <$> f
      <*? (flip fmap <$> m)

-- | No @'Monad' f@ constraint is needed.
instance Selective f => Selective (ExceptT e f) where
    select (ExceptT (Transformers.ExceptT meab)) (ExceptT (Transformers.ExceptT mef)) = ExceptT $ Transformers.ExceptT
        $ commute <$> meab
        <*? (swapFunctionEither <$> mef)
        where
            commute :: Either e (Either a b) -> Either a (Either e b)
            commute (Left e) = Right (Left e)
            commute (Right (Left a)) = Left a
            commute (Right (Right b)) = Right (Right b)

            swapFunctionEither :: Either e (a -> b) -> a -> Either e b
            swapFunctionEither (Left e) _ = Left e
            swapFunctionEither (Right fab) a = Right (fab a)

-- | No @'Monad' f@ constraint is needed.
instance (Selective f, Monoid e) => Alternative (ExceptT e f) where
    empty = ExceptT $ Transformers.ExceptT $ pure $ Left mempty
    ExceptT (Transformers.ExceptT mx) <|> ExceptT (Transformers.ExceptT my)
        = ExceptT $ Transformers.ExceptT
        $ fmap Right <$> mx
        <*? ( either ((Left .) . mappend) (flip (const Right)) <$> my)

-- | Convert back to the newtype.
fromTransformers :: Transformers.ExceptT e m a -> ExceptT e m a
fromTransformers = ExceptT

type Except e = ExceptT e Identity

#if MIN_VERSION_transformers(0,5,6)
except :: Monad m => Either e a -> ExceptT e m a
#else
except :: Either e a -> Except e a
#endif
except = ExceptT . Transformers.except

runExcept :: Except e a -> Either e a
runExcept = Transformers.runExcept . toTransformers

mapExcept :: (Either e a -> Either e' b) -> Except e a -> Except e' b
mapExcept f = ExceptT . Transformers.mapExcept f . toTransformers

withExcept :: (e -> e') -> Except e a -> Except e' a
withExcept f = ExceptT . Transformers.withExcept f . toTransformers

runExceptT :: ExceptT e m a -> m (Either e a)
runExceptT = Transformers.runExceptT . toTransformers

mapExceptT :: (m (Either e a) -> n (Either e' b)) -> ExceptT e m a -> ExceptT e' n b
mapExceptT f = ExceptT . Transformers.mapExceptT f . toTransformers

withExceptT :: Functor m => (e -> e') -> ExceptT e m a -> ExceptT e' m a
withExceptT f = ExceptT . Transformers.withExceptT f . toTransformers

throwE :: Monad m => e -> ExceptT e m a
throwE = ExceptT . Transformers.throwE

catchE :: Monad m => ExceptT e m a -> (e -> ExceptT e' m a) -> ExceptT e' m a
catchE action continuation = ExceptT $ Transformers.catchE (toTransformers action) (toTransformers . continuation)

liftCallCC :: CallCC m (Either e a) (Either e b) -> CallCC (ExceptT e m) a b
liftCallCC callCC caller = ExceptT $ Transformers.liftCallCC callCC (toTransformers . caller . (ExceptT .))

liftListen :: Monad m => Listen w m (Either e a) -> Listen w (ExceptT e m) a
liftListen listen (ExceptT action) = ExceptT $ Transformers.liftListen listen action

liftPass :: Monad m => Pass w m (Either e a) -> Pass w (ExceptT e m) a
liftPass pass (ExceptT action) = ExceptT $ Transformers.liftPass pass action
