# Selective applicative functors

This is a study of *selective applicative functors*, an abstraction between `Applicative` and `Monad`:

```haskell
-- Note: the laws are still in flux. They still look unsatisfactory, so any ideas
-- on how to improve them yet keep Const and Validation instances are welcome!
--
-- Law: If fmap Left x /= fmap Right x then
--      * handle f (fmap Left  x) == f <*> x
--      * handle f (fmap Right x) == x
--
-- For example, when f = Maybe we have:
--      * handle f (Just (Left  a)) == f <*> x
--      * handle f (Just (Right b)) == x
--      * handle f Nothing is not constrained, allowing the implementation to
--        select between the two above behaviours. The default implementation
--        provided for a Monad f skips the effect: handle f Nothing == Nothing.
class Applicative f => Selective f where
    handle :: f (a -> b) -> f (Either a b) -> f b
```

You can think of `handle` as a *selective function application*: you apply the
function only when given a value of type `Left a`. Otherwise, you skip it (along
with all its effects) and return the `b` from `Right b`. Intuitively, `handle`
allows you to *efficiently* handle an error, which we often represent by `Left a`
in Haskell.

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
apS f = handle f . fmap Left
```

The `select` function is a natural generalisation of `handle`: instead of
skipping one unnecessary effect, it selects which of the two given effectful
functions to apply to a given argument. It is possible to implement `select` in
terms of `handle`, which is a good puzzle (give it a try!):

```haskell
select :: Selective f => f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
select = ... -- Try to figure out the implementation!
```

Finally, any `Monad` is `Selective`:

```haskell
handleM :: Monad f => f (a -> b) -> f (Either a b) -> f b
handleM mf mx = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> pure b
```

Selective functors are sufficient for implementing many conditional constructs,
which traditionally require the (much more powerful) `Monad` type class.
For example:

```haskell
-- | Branch on a Boolean value, skipping unnecessary effects.
ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS i t f = select (fmap const f) (fmap const t) $
    fmap (\b -> if b then Right () else Left ()) i

-- | Conditionally apply an effect.
whenS :: Selective f => f Bool -> f () -> f ()
whenS x act = ifS x act (pure ())

-- | Keep checking a given effectful condition while it holds.
whileS :: Selective f => f Bool -> f ()
whileS act = whenS act (whileS act)

-- | A lifted version of lazy Boolean OR.
(<||>) :: Selective f => f Bool -> f Bool -> f Bool
(<||>) a b = ifS a (pure True) b

-- | A lifted version of 'any'. Retains the short-circuiting behaviour.
anyS :: Selective f => (a -> f Bool) -> [a] -> f Bool
anyS p = foldr ((<||>) . p) (pure False)
```

See more examples in [src/Control/Selective.hs](src/Control/Selective.hs).

## Static analysis of selective functors

Like applicative functors, selective functors can be analysed statically.
We can make the `Const` functor an instance of `Selective` as follows.

```haskell
instance Monoid m => Selective (Const m) where
    handle = handleA
```

This might look suspicious, but since `Const m a` has no `a`, it is not
required to skip any effects. Therefore, you can use it to extract the
static structure of a given selective computation.

The `Validation` instance is perhaps a bit more interesting.

```haskell
data Validation e a = Failure e | Success a

instance Functor (Validation e) where
    fmap _ (Failure e) = Failure e
    fmap f (Success a) = Success (f a)

instance Semigroup e => Applicative (Validation e) where
    pure = Success
    Failure e1 <*> Failure e2 = Failure (e1 <> e2)
    Failure e1 <*> Success _  = Failure e1
    Success _  <*> Failure e2 = Failure e2
    Success f  <*> Success a  = Success (f a)

instance Semigroup e => Selective (Validation e) where
    handle _ (Success (Right b)) = Success b
    handle f (Success (Left  a)) = f <*> Success a
    handle _ (Failure e        ) = Failure e
```

Here, the last line is particularly interesting: unlike the `Const`
instance, we choose to actually skip the handler effect in case of
`Failure`. This allows us not to report any validation errors which
are hidden behind a failed conditional.

Let's clarify this with an example. Here we define a function to
construct a `Shape` (a circle or a rectangle) given a choice of the
shape `s` and the shape's parameters (`r`, `w`, `h`) in a selective
context `f`.

```haskell
type Radius = Int
type Width  = Int
type Height = Int

data Shape = Circle Radius | Rectangle Width Height deriving Show

shape :: Selective f => f Bool -> f Radius -> f Width -> f Height -> f Shape
shape s r w h = ifS s (Circle <$> r) (Rectangle <$> w <*> h)
```

We choose `f = Validation [String]` to reports the errors that occurred
when parsing a value. Let's see how it works.

```haskell
> shape (Success True) (Success 10) (Failure ["no width"]) (Failure ["no height"])
> Success (Circle 10)

> shape (Success False) (Failure ["no radius"]) (Success 20) (Success 30)
> Success (Rectangle 20 30)

> shape (Success False) (Failure ["no radius"]) (Success 20) (Failure ["no height"])
> Failure ["no height"]

> shape (Success False) (Failure ["no radius"]) (Failure ["no width"]) (Failure ["no height"])
> Failure ["no width","no height"]

> shape (Failure ["no choice"]) (Failure ["no radius"]) (Success 20) (Failure ["no height"])
> Failure ["no choice"]
```

In the last example, since we failed to parse which shape has been chosen,
we do not report any subsequent errors. But it doesn't mean we are short-circuiting
the validation. We will keep accumulating errors as soon as we get out of the
opaque conditional, as demonstrated below.


```haskell
twoShapes :: Selective f => f Shape -> f Shape -> f (Shape, Shape)
twoShapes s1 s2 = (,) <$> s1 <*> s2

> s1 = shape (Failure ["no choice 1"]) (Failure ["no radius 1"]) (Success 20) (Failure ["no height 1"])
> s2 = shape (Success False) (Failure ["no radius 2"]) (Success 20) (Failure ["no height 2"])
> twoShapes s1 s2
> Failure ["no choice 1","no height 2"]
```
