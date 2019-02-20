# Selective applicative functors

This is a study of *selective applicative functors*, an abstraction between
`Applicative` and `Monad`:

```haskell
class Applicative f => Selective f where
    select :: f (Either a b) -> f (a -> b) -> f b

-- | An operator alias for 'select'.
(<*?) :: Selective f => f (Either a b) -> f (a -> b) -> f b
(<*?) = select

infixl 4 <*?
```

Think of `select` as a *selective function application*: you **must apply** the function
of type `a -> b` when given a value of type `Left a`, but you **may skip** the
function and associated effects, and simply return `b` when given `Right b`.

Note that you can write a function with this type signature using
`Applicative` functors, but it will always execute the effects associated
with the second argument, hence being potentially less efficient:

```haskell
selectA :: Applicative f => f (Either a b) -> f (a -> b) -> f b
selectA x f = (\e f -> either f id e) <$> x <*> f
```

`Selective` is more powerful than `Applicative`: you can recover the
application operator `<*>` as follows (I'll use the suffix `S` to
denote `Selective` equivalents of commonly known functions).

```haskell
apS :: Selective f => f (a -> b) -> f a -> f b
apS f x = select (Left <$> f) (flip ($) <$> x)
```

Here we wrap a given function `a -> b` into `Left` and turn the value `a`
into a function `($a)`, which simply feeds itself to the function `a -> b`
yielding `b` as desired. Note: `apS` is a perfectly legal
application operator `<*>`, i.e. it satisfies the laws dictated by the
`Applicative` type class as long as [the laws](#laws) of the `Selective`
type class hold.

The `branch` function is a natural generalisation of `select`: instead of
skipping an unnecessary effect, it chooses which of the two given effectful
functions to apply to a given argument; the other effect is unnecessary. It
is possible to implement `branch` in terms of `select`, which is a good
puzzle (give it a try!).

```haskell
branch :: Selective f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch = ... -- Try to figure out the implementation!
```

Finally, any `Monad` is `Selective`:

```haskell
selectM :: Monad f => f (Either a b) -> f (a -> b) -> f b
selectM mx mf = do
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
ifS i t e = branch (bool (Right ()) (Left ()) <$> i) (const <$> t) (const <$> e)

-- | Conditionally perform an effect.
whenS :: Selective f => f Bool -> f () -> f ()
whenS x act = ifS x act (pure ())

-- | Keep checking an effectful condition while it holds.
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
orElse x = select (Right <$> x) . fmap (\y e -> first (e <>) y)
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
    f <$> select x y = select (second f <$> x) ((f .) <$> y)
    ```

* (F2) Apply a pure function to the `Left` case of the first argument:
    ```haskell
    select (first f <$> x) y = select x ((. f) <$> y)
    ```

* (F3) Apply a pure function to the second argument:
    ```haskell
    select x (f <$> y) = select (first (flip f) <$> x) (flip ($) <$> y)
    ```

* (P1) Selective application of a pure function:
    ```haskell
    select x (pure y) = either y id <$> x
    ```

* (P2) Selective application of a function to a pure 'Left' value:
    ```haskell
    select (pure (Left x)) y = ($x) <$> y
    ```

* (A1) Associativity:
    ```haskell
    select x (select y z) = select (select (f <$> x) (g <$> y)) (h <$> z)
      where
        f x = Right <$> x
        g y = \a -> bimap (,a) ($a) y
        h z = uncurry z

    -- or in operator form:

    x <*? (y <*? z) = (f <$> x) <*? (g <$> y) <*? (h <$> z)
    ```

Note that there is no law for selective application of a function to a
pure `Right` value, i.e. we do not require that the following holds:

```haskell
select (pure (Right x)) y = pure x
```

In particular, the following is allowed too:

```haskell
select (pure (Right x)) y = const x <$> y
```

We therefore allow `select` to be selective about effects in this case.
A consequence of the above laws is that `apS` satisfies `Applicative` laws.
However, we choose not to require that `apS = <*>`, since this forbids some
interesting instances, such as `Validation` defined below.

If `f` is also a `Monad`, we require that `select = selectM`.

## Static analysis of selective functors

Like applicative functors, selective functors can be analysed statically.
We can make the `Const` functor an instance of `Selective` as follows.

```haskell
instance Monoid m => Selective (Const m) where
    select = selectA
```

Although we don't need the function `Const m (a -> b)` (note that
`Const m (Either a b)` holds no values of type `a`), we choose to
accumulate the effects associated with it. This allows us to extract
the static structure of any selective computation very similarly
to how this is done with applicative computations.

The `Validation` instance is perhaps a bit more interesting.

```haskell
data Validation e a = Failure e | Success a deriving (Functor, Show)

instance Semigroup e => Applicative (Validation e) where
    pure = Success
    Failure e1 <*> Failure e2 = Failure (e1 <> e2)
    Failure e1 <*> Success _  = Failure e1
    Success _  <*> Failure e2 = Failure e2
    Success f  <*> Success a  = Success (f a)

instance Semigroup e => Selective (Validation e) where
    select (Success (Right b)) _ = Success b
    select (Success (Left  a)) f = Success ($a) <*> f
    select (Failure e        ) _ = Failure e
```

Here, the last line is particularly interesting: unlike the `Const`
instance, we choose to actually skip the function effect in case of
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

We choose `f = Validation [String]` to report the errors that occurred
when parsing a value. Let's see how it works.

```haskell
> shape (Success True) (Success 10) (Failure ["no width"]) (Failure ["no height"])
Success (Circle 10)

> shape (Success False) (Failure ["no radius"]) (Success 20) (Success 30)
Success (Rectangle 20 30)

> shape (Success False) (Failure ["no radius"]) (Success 20) (Failure ["no height"])
Failure ["no height"]

> shape (Success False) (Failure ["no radius"]) (Failure ["no width"]) (Failure ["no height"])
Failure ["no width","no height"]

> shape (Failure ["no choice"]) (Failure ["no radius"]) (Success 20) (Failure ["no height"])
Failure ["no choice"]
```

In the last example, since we failed to parse which shape has been chosen,
we do not report any subsequent errors. But it doesn't mean we are short-circuiting
the validation. We will continue accumulating errors as soon as we get out of the
opaque conditional, as demonstrated below.


```haskell
twoShapes :: Selective f => f Shape -> f Shape -> f (Shape, Shape)
twoShapes s1 s2 = (,) <$> s1 <*> s2

> s1 = shape (Failure ["no choice 1"]) (Failure ["no radius 1"]) (Success 20) (Failure ["no height 1"])
> s2 = shape (Success False) (Failure ["no radius 2"]) (Success 20) (Failure ["no height 2"])
> twoShapes s1 s2
Failure ["no choice 1","no height 2"]
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

## Further reading

* A blog post introducing selective applicative functors: https://blogs.ncl.ac.uk/andreymokhov/selective.
