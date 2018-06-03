# Selective applicative functors

This is a study of *selective applicative functors*, an abstraction between `Applicative` and `Monad`: 

```haskell
-- Laws: 1) f <?*> fmap Left  x == f <*> x
--       2) f <?*> fmap Right x == x
--
class Applicative f => Selective f where
    (<?*>) :: f (a -> b) -> f (Either a b) -> f b
```

You can think of `<?*>` as a *selective function application*: you apply it only when given a value of
type `Left a`. Otherwise, you skip it (along with all its effects) and return the `b` from `Right b`.

Note that you can write a function with this type signature using `Applicative`, but it will have
different behaviour -- it will always execute the effects associated with the function:

```haskell
selectA :: Applicative f => f (a -> b) -> f (Either a b) -> f b
selectA f x = either <$> f <*> pure id <*> x
```

`Selective` is more powerful than `Applicative`: you can recover the application operator `<*>` as follows.

```haskell
applyS :: Selective f => f (a -> b) -> f a -> f b
applyS f x = f <?*> fmap Left x
```

Finally, any `Monad` is `Selective`: 

```haskell
selectM :: Monad f => f (a -> b) -> f (Either a b) -> f b
selectM mf mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> return b
```

Selective functors are sufficient for implementing many conditional constructs, for example:

```haskell
eitherS :: Selective f => f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
eitherS l r x = r <?*> (fmap (fmap Right) l <?*> fmap (fmap Left) x)

ite :: Selective f => f Bool -> f a -> f a -> f a
ite i t e = eitherS (fmap const t) (fmap const e) $
    fmap (\b -> if b then Left () else Right ()) i
```
