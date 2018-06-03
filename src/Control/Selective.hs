module Control.Selective where

-- Selective applicative functor.
--
-- Laws: 1) handle f (fmap Left  x) == f <*> x  (free teorem)
--       2) handle f (fmap Right x) == x
--
--       3) select f g (fmap Left  x) == f <*> x
--       4) select f g (fmap Right x) == g <*> x
--
class Applicative f => Selective f where
    handle :: f (a -> b) -> f (Either a b) -> f b
    handle f = select f (pure id)

    select :: f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
    select l r x = handle r (handle (fmap (fmap Right) l) (fmap (fmap Left) x))

-- This could be moved to the type class
handleRight :: Selective f => f (b -> a) -> f (Either a b) -> f a
handleRight f = handle f . fmap mirror
  where
    mirror (Left  x) = Right x
    mirror (Right x) = Left  x

-- We can recover <*> from <?*>
apS :: Selective f => f (a -> b) -> f a -> f b
apS f = handle f . fmap Left

-- This is the only possible implementation of <?*> using Applicative
-- It always performs f's effects
selectA :: Applicative f => f (a -> b) -> f (Either a b) -> f b
selectA f x = either <$> f <*> pure id <*> x

-- Any Monad is Selective
handleM :: Monad f => f (a -> b) -> f (Either a b) -> f b
handleM mf mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> return b

selectM :: Monad f => f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
selectM mf mg mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> fmap ($b) mg

-- Many useful Monad combinators that can be implemented with Selective

whenS :: Selective f => f Bool -> f () -> f ()
whenS x act = handle (act *> pure id) (fmap (\b -> if b then Left () else Right ()) x)

fromMaybeS :: Selective f => f a -> f (Maybe a) -> f a
fromMaybeS x = handle (fmap const x) . fmap (maybe (Left ()) Right)

ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS i t e = select (fmap const t) (fmap const e) $
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
    handle = handleM
    select = selectM
