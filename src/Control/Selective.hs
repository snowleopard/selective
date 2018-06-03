module Control.Selective (
    -- * Type class
    Selective (..), handleRight, apS, handleA, selectA, handleM, selectM,

    -- * Conditional combinators
    ifS, whenS, fromMaybeS, whileS, (<||>), (<&&>), anyS, allS

    ) where

-- Selective applicative functor.
--
-- Laws: 1) handle f (fmap Left  x) == f <*> x  (free theorem)
--       2) handle f (fmap Right x) == x
--
--       3) select f g (fmap Left  x) == f <*> x
--       4) select f g (fmap Right x) == g <*> x
--
class Applicative f => Selective f where
    {-# MINIMAL handle | select #-}
    handle :: f (a -> b) -> f (Either a b) -> f b
    handle f = select f (pure id)

    select :: f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
    select l r = handle r . handle (fmap (fmap Right) l) . fmap (fmap Left)

-- This could be moved to the type class
handleRight :: Selective f => f (b -> a) -> f (Either a b) -> f a
handleRight f = handle f . fmap mirror
  where
    mirror (Left  x) = Right x
    mirror (Right x) = Left  x

-- We can recover <*> from 'handle'
apS :: Selective f => f (a -> b) -> f a -> f b
apS f = handle f . fmap Left

-- This is the only possible implementation of 'handle' using Applicative
-- It always performs f's effects
handleA :: Applicative f => f (a -> b) -> f (Either a b) -> f b
handleA f x = either <$> f <*> pure id <*> x

selectA :: Applicative f => f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
selectA f g x = either <$> f <*> g <*> x

-- Any Monad is Selective
handleM :: Monad f => f (a -> b) -> f (Either a b) -> f b
handleM mf mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> pure b

selectM :: Monad f => f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
selectM mf mg mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> fmap ($b) mg

-- Many useful Monad combinators that can be implemented with Selective

ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS i t f = select (fmap const f) (fmap const t) $
    fmap (\b -> if b then Right () else Left ()) i

whenS :: Selective f => f Bool -> f () -> f ()
whenS x act = ifS x act (pure ())

fromMaybeS :: Selective f => f a -> f (Maybe a) -> f a
fromMaybeS x = handle (fmap const x) . fmap (maybe (Left ()) Right)

whileS :: Selective f => f Bool -> f ()
whileS act = whenS act (whileS act)

(<||>) :: Selective f => f Bool -> f Bool -> f Bool
(<||>) a b = ifS a (pure True) b

(<&&>) :: Selective f => f Bool -> f Bool -> f Bool
(<&&>) a b = ifS a b (pure False)

anyS :: Selective f => (a -> f Bool) -> [a] -> f Bool
anyS p = foldr ((<||>) . p) (pure False)

allS :: Selective f => (a -> f Bool) -> [a] -> f Bool
allS p = foldr ((<&&>) . p) (pure True)

-- Instances

-- Try: ite (pure True) (print 1) (print 2)
instance Selective IO where
    handle = handleM
    select = selectM
