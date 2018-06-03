module Control.Selective where

-- Selective applicative functor.
--
-- Laws: 1) f <?*> fmap Left  x == f <*> x
--       2) f <?*> fmap Right x == x
--
class Applicative f => Selective f where
    (<?*>) :: f (a -> b) -> f (Either a b) -> f b

-- This could be moved to the type class
(<*?>) :: Selective f => f (Either a b) -> f (b -> a) -> f a
x <*?> f = f <?*> fmap mirror x
  where
    mirror (Left  x) = Right x
    mirror (Right x) = Left  x

-- We can recover <*> from <?*>
apS :: Selective f => f (a -> b) -> f a -> f b
apS f x = f <?*> fmap Left x

-- This is the only possible implementation of <?*> using Applicative
-- It always performs f's effects
selectA :: Applicative f => f (a -> b) -> f (Either a b) -> f b
selectA f x = either <$> f <*> pure id <*> x

-- Any Monad is Selective
selectM :: Monad f => f (a -> b) -> f (Either a b) -> f b
selectM mf mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> return b

-- Many useful Monad combinators that can be implemented with Selective

whenS :: Selective f => f Bool -> f () -> f ()
whenS x act = act *> pure id <?*> fmap (\b -> if b then Left () else Right ()) x

fromMaybeS :: Selective f => f a -> f (Maybe a) -> f a
fromMaybeS x m = fmap const x <?*> fmap (maybe (Left ()) Right) m

eitherS :: Selective f => f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
eitherS l r x = r <?*> (fmap (fmap Right) l <?*> fmap (fmap Left) x)

ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS i t e = eitherS (fmap const t) (fmap const e) $
    fmap (\b -> if b then Left () else Right ()) i

whileS :: Selective f => f Bool -> f ()
whileS act = whenS act (whileS act)

(||^) :: Selective f => f Bool -> f Bool -> f Bool
(||^) a b = ifS a (pure True) b

(&&^) :: Selective f => f Bool -> f Bool -> f Bool
(&&^) a b = ifS a b (pure False)

-- Instances

-- Try: ite (pure True) (print 1) (print 2)
instance Selective IO where
    (<?*>) = selectM
