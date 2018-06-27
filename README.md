# Selective applicative functors

This is a study of *selective applicative functors*, an abstraction between `Applicative` and `Monad`:

```haskell
class Applicative f => Selective f where
    handle :: f (Either a b) -> f (a -> b) -> f b

-- | An operator alias for 'handle'.
(<*?) :: Selective f => f (Either a b) -> f (a -> b) -> f b
(<*?) = handle

infixl 4 <*?
```

Think of `handle` as a *selective function application*: you apply a handler
function of type `a -> b` when given a value `Left a`, but can skip the
handler (along with its effects) in the case of `Right b`. Intuitively,
`handle` allows you to *efficiently* handle errors, i.e. perform the
error-handling effects only when needed.

Note that you can write a function with this type signature using
`Applicative` functors, but it will always execute the effects
associated with the handler, hence being less efficient:

```haskell
handleA :: Applicative f => f (Either a b) -> f (a -> b) -> f b
handleA x f = (\e f -> either f id e) <$> x <*> f
```

`Selective` is more powerful than `Applicative`: you can recover the
application operator `<*>` as follows (I'll use the suffix `S` to
denote `Selective` equivalents of commonly known functions).

```haskell
apS :: Selective f => f (a -> b) -> f a -> f b
apS f x = handle (Left <$> f) (flip ($) <$> x)
```

Here we tag a given function `a -> b` as an error and turn a value `a`
into an error-handling function `($a)`, which simply applies itself to the
error `a -> b` yielding `b` as desired. Note: `apS` is a perfectly legal
application operator `<*>`, i.e. it satisfies the laws dictated by the
`Applicative` type class as long as [the laws](#laws) of the `Selective`
type class hold.

The `select` function is a natural generalisation of `handle`: instead of
skipping one unnecessary effect, it selects which of the two given effectful
functions to apply to a given argument. It is possible to implement `select` in
terms of `handle`, which is a good puzzle (give it a try!):

```haskell
select :: Selective f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
select = ... -- Try to figure out the implementation!
```

Finally, any `Monad` is `Selective`:

```haskell
handleM :: Monad f => f (Either a b) -> f (a -> b) -> f b
handleM mx mf = do
    x <- mx
    case x of
        Left  a -> fmap ($a) mf
        Right b -> pure b
```

Selective functors are sufficient for implementing many conditional constructs,
which traditionally require the (more powerful) `Monad` type class. For example:

```haskell
-- | Branch on a Boolean value, skipping unnecessary effects.
ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS i t e = select (bool (Right ()) (Left ()) <$> i) (const <$> t) (const <$> e)

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

-- | Return the first @Right@ value. If both are @Left@'s, accumulate errors.
orElse :: (Selective f, Semigroup e) => f (Either e a) -> f (Either e a) -> f (Either e a)
orElse x = handle (Right <$> x) . fmap (\y e -> first (e <>) y)
```

See more examples in [src/Control/Selective.hs](src/Control/Selective.hs).

## Laws

Instances of the `Selective` type class must satisfy a few laws to make
it possible to refactor selective computations. These laws also allow us
to establish a formal relation with the `Applicative` and `Monad` type
classes. The laws are complex, but I couldn't figure out how to simplify
them. Please let me know if you find an improvement.

* (F1) Apply a pure function to the result:
    ```haskell
    f <$> handle x y = handle (second f <$> x) ((f .) <$> y)
    ```

* (F2) Apply a pure function to the left (error) branch:
    ```haskell
    handle (first f <$> x) y = handle x ((. f) <$> y)
    ```

* (F3) Apply a pure function to the handler:
    ```haskell
    handle x (f <$> y) = handle (first (flip f) <$> x) (flip ($) <$> y)
    ```

* (P1) Apply a pure handler:
    ```haskell
    handle x (pure y) = either y id <$> x
    ```

* (P2) Handle a pure error:
    ```haskell
    handle (pure (Left x)) y = ($x) <$> y
    ```

* (A1) Associativity:
    ```haskell
    handle x (handle y z) = handle (handle (f <$> x) (g <$> y)) (h <$> z)
      where
        f x = Right <$> x
        g y = \a -> bimap (,a) ($a) y
        h z = uncurry z

    -- or in operator form:

    x <*? (y <*? z) = (f <$> x) <*? (g <$> y) <*? (h <$> z)
    ```

Note that there is no law for handling a pure value, i.e. we do not require
that the following holds:

```haskell
handle (pure (Right x)) y = pure x
```

In particular, the following is allowed too:

```haskell
handle (pure (Right x)) y = const x <$> y
```

We therefore allow `handle` to be selective about effects in this case.
A consequence of the above laws is that `apS` satisfies `Applicative` laws.
However, we choose not to require that `apS = <*>`, since this forbids some
interesting instances, such as `Validation` defined below.

If `f` is also a `Monad`, we require that `handle = handleM`.

## Static analysis of selective functors

Like applicative functors, selective functors can be analysed statically.
We can make the `Const` functor an instance of `Selective` as follows.

```haskell
instance Monoid m => Selective (Const m) where
    handle = handleA
```

Although we don't need the handler `Const m (a -> b)` (note that
`Const m (Either a b)` holds no values of type `a`), we choose to
accumulate the effects associated with it. This allows us to extract
the static structure of any selective computation very similarly
to how this is done with applicative computations.

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
    handle (Success (Right b)) _ = Success b
    handle (Success (Left  a)) f = flip ($) <$> Success a <*> f
    handle (Failure e        ) _ = Failure e
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

## Alternative formulations

There are other ways of expressing selective functors in Haskell and most of them are
compositions of applicative functors and the `Either` monad. Below I list a few
examples:

```haskell
-- Alternative type classes for selective functors. They all come with an
-- additional requirement that we run effects from left to right.

-- Composition of Applicative and Either monad
class Applicative f => SelectiveA f where
    (|*|) :: f (Either e (a -> b)) -> f (Either e a) -> f (Either e b)

-- Composition of Starry and Either monad
-- See: https://duplode.github.io/posts/applicative-archery.html
class Applicative f => SelectiveS f where
    (|.|) :: f (Either e (b -> c)) -> f (Either e (a -> b)) -> f (Either e (a -> c))

-- Composition of Monoidal and Either monad
-- See: http://blog.ezyang.com/2012/08/applicative-functors/
class Applicative f => SelectiveM f where
    (|**|) :: f (Either e a) -> f (Either e b) -> f (Either e (a, b))
```

I believe these formulations are equivalent to `Selective` defined above,
but I have not proved the equivalence formally. I chose the most
minimalistic definition of the type class, but the above alternatives
are worth consideration too. In particular, `SelectiveS` has a much nicer
associativity law, which is just `(x |.| y) |.| z = x |.| (y |.| z)`.

## Do we still need monads?

Yes! Here is what selective functors cannot do: `join :: Selective f => f (f a) -> f a`.
