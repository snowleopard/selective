# Selective applicative functors

This is a study of *selective applicative functors*, an abstraction between `Applicative` and `Monad`:

```haskell
-- Laws: 1) handle f (fmap Left  x) == f <*> x  (free theorem)
--       2) handle f (fmap Right x) == x
--
--       3) select f g (fmap Left  x) == f <*> x
--       4) select f g (fmap Right x) == g <*> x
--
class Applicative f => Selective f where
    {-# MINIMAL handle | select #-}
    handle :: f (a -> b) -> f (Either a b) -> f b
    select :: f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
```

You can think of `handle` as a *selective function application*: you apply it
only when given a value of type `Left a`. Otherwise, you skip it (along with all
its effects) and return the `b` from `Right b`. Intuitively, `handle` allows
you to efficiently handle an error (idiomatically represented by `Left a`).

Note that you can write a function with this type signature using `Applicative`,
but it will have different behaviour -- it will always execute the effects
associated with the handler, hence being less efficient.

```haskell
handleA :: Applicative f => f (a -> b) -> f (Either a b) -> f b
handleA f x = either <$> f <*> pure id <*> x
```

`Selective` is more powerful than `Applicative`: you can recover the
application operator `<*>` as follows.

```haskell
apS :: Selective f => f (a -> b) -> f a -> f b
apS f x = f <?*> fmap Left x
```

The `select` method is a natural generalisation of `handle`: instead of
skipping unnecessary effects, it selects which of the two given effectful
functions to apply to a given argument. It is possible to implement `select` in
terms of `handle`, which is a good puzzle (give it a try!), and vice versa, so
it makes sense to keep them both in the type class.

Finally, any `Monad` is `Selective`:

```haskell
handleM :: Monad f => f (a -> b) -> f (Either a b) -> f b
handleM mf mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> return b
```

Selective functors are sufficient for implementing many conditional constructs,
which traditionally require the (much more powerful) `Monad` type class.
For example:

```haskell
ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS i t f = select (fmap const f) (fmap const t) $
    fmap (\b -> if b then Right () else Left ()) i

whenS :: Selective f => f Bool -> f () -> f ()
whenS x act = ifS x act (pure ())

whileS :: Selective f => f Bool -> f ()
whileS act = whenS act (whileS act)
```

See more examples in [src/Control/Selective.hs](src/Control/Selective.hs).
