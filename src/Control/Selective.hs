{-# LANGUAGE CPP, LambdaCase, TupleSections, DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DerivingVia #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Selective
-- Copyright  : (c) Andrey Mokhov 2018-2024
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- This is a library for /selective applicative functors/, or just
-- /selective functors/ for short, an abstraction between applicative functors
-- and monads, introduced in this paper: https://dl.acm.org/doi/10.1145/3341694.
--
-----------------------------------------------------------------------------
module Control.Selective (
    -- * Type class
    Selective (..), (<*?), branch, selectA, selectT, apS, selectM,

    -- * Conditional combinators
    ifS, whenS, fromMaybeS, orElse, andAlso, untilRight, whileS, (<||>), (<&&>),
    foldS, anyS, allS, bindS, Cases, casesEnum, cases, matchS, matchM,

    -- * Selective functors
    SelectA (..), SelectM (..), Over (..), Under (..), Validation (..),

    -- * Miscellaneous
    swapEither, ComposeEither (..), ComposeTraversable (..)
    ) where

import Control.Applicative
import Control.Applicative.Lift
import Control.Arrow
import Control.Monad.ST
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import Control.Monad.Trans.RWS
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Data.Bool
import Data.Function
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.List.NonEmpty
import Data.Proxy
import Data.Semigroup (Semigroup (..))
import GHC.Conc (STM)

import qualified Control.Monad.Trans.RWS.Strict    as S
import qualified Control.Monad.Trans.State.Strict  as S
import qualified Control.Monad.Trans.Writer.Strict as S

-- | Selective applicative functors. You can think of 'select' as a selective
-- function application: when given a value of type 'Left' @a@, you __must apply__
-- the given function, but when given a 'Right' @b@, you __may skip__ the
-- function and associated effects, and simply return the @b@.
--
-- Note that it is not a requirement for selective functors to skip unnecessary
-- effects. It may be counterintuitive, but this makes them more useful. Why?
-- Typically, when executing a selective computation, you would want to skip the
-- effects (saving work); but on the other hand, if your goal is to statically
-- analyse a given selective computation and extract the set of all possible
-- effects (without actually executing them), then you do not want to skip any
-- effects, because that defeats the purpose of static analysis.
--
-- The type signature of 'select' is reminiscent of both '<*>' and '>>=', and
-- indeed a selective functor is in some sense a composition of an applicative
-- functor and the 'Either' monad.
--
-- Laws:
--
-- * Identity:
--
-- @
-- x \<*? pure id = either id id \<$\> x
-- @
--
-- * Distributivity; note that @y@ and @z@ have the same type @f (a -> b)@:
--
-- @
-- pure x \<*? (y *\> z) = (pure x \<*? y) *\> (pure x \<*? z)
-- @
--
-- * Associativity:
--
-- @
-- x \<*? (y \<*? z) = (f \<$\> x) \<*? (g \<$\> y) \<*? (h \<$\> z)
--   where
--     f x = Right \<$\> x
--     g y = \a -\> bimap (,a) ($a) y
--     h z = uncurry z
-- @
--
-- * Monadic 'select' (for selective functors that are also monads):
--
-- @
-- select = selectM
-- @
--
-- There are also a few useful theorems:
--
-- * Apply a pure function to the result:
--
-- @
-- f \<$\> select x y = select (fmap f \<$\> x) (fmap f \<$\> y)
-- @
--
-- * Apply a pure function to the @Left@ case of the first argument:
--
-- @
-- select (first f \<$\> x) y = select x ((. f) \<$\> y)
-- @
--
-- * Apply a pure function to the second argument:
--
-- @
-- select x (f \<$\> y) = select (first (flip f) \<$\> x) ((&) \<$\> y)
-- @
--
-- * Generalised identity:
--
-- @
-- x \<*? pure y = either y id \<$\> x
-- @
--
-- * A selective functor is /rigid/ if it satisfies '<*>' @=@ 'apS'. The
-- following /interchange/ law holds for rigid selective functors:
--
-- @
-- x *\> (y \<*? z) = (x *\> y) \<*? z
-- @
--
-- If f is also a 'Monad', we require that 'select' = 'selectM', from which one
-- can prove '<*>' @=@ 'apS'.
class Applicative f => Selective f where
    select :: f (Either a b) -> f (a -> b) -> f b

{- Why do we have skew associativity, where we can reassociate effects to the
   left but not to the right?

   The following two tables, which list all possible combinations of effect
   execution and skipping, might give you some intuition on why this happens.

     ---------------
     (x <*? y) <*? z
     ---------------
      1     0      0
      1     1      0
      1     0      1
      1     1      1

     ---------------
     x <*? (y <*? z)
     ---------------
     1      0     0
     1      1     0
     1      1     1

   A key observation is that when effects are associated to the right, we can't
   skip the effect y and execute the effect z: combination 101 is impossible.
-}

-- | An operator alias for 'select', which is sometimes convenient. It tries to
-- follow the notational convention for 'Applicative' operators. The angle
-- bracket pointing to the left means we always use the corresponding value.
-- The value on the right, however, may be skipped, hence the question mark.
(<*?) :: Selective f => f (Either a b) -> f (a -> b) -> f b
(<*?) = select

infixl 4 <*?

-- | The 'branch' function is a natural generalisation of 'select': instead of
-- skipping an unnecessary effect, it chooses which of the two given effectful
-- functions to apply to a given argument; the other effect is unnecessary. It
-- is possible to implement 'branch' in terms of 'select', which is a good
-- puzzle (give it a try!).
--
-- We can also implement 'select' via 'branch':
--
-- @
-- selectB :: Selective f => f (Either a b) -> f (a -> b) -> f b
-- selectB x y = branch x y (pure id)
-- @
--
branch :: Selective f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch x l r = fmap (fmap Left) x <*? fmap (fmap Right) l <*? r

-- | We can write a function with the type signature of 'select' using the
-- 'Applicative' type class, but it will always execute the effects associated
-- with the second argument, hence being potentially less efficient.
selectA :: Applicative f => f (Either a b) -> f (a -> b) -> f b
selectA x y = (\e f -> either f id e) <$> x <*> y

-- | For traversable functors, we can implement 'select' in another interesting
-- way: the effects associated with the second argument can be skipped as long
-- as the first argument contains only 'Right' values.
selectT :: Traversable f => f (Either a b) -> f (a -> b) -> f b
selectT x y = case sequenceA x of
    Left  a  -> ($a) <$> y
    Right fb -> fb

{-| Recover the application operator '<*>' from 'select'. /Rigid/ selective
functors satisfy the law '<*>' @=@ 'apS' and furthermore, the resulting
applicative functor satisfies all laws of 'Applicative':

* Identity:

    > pure id <*> v = v

* Homomorphism:

    > pure f <*> pure x = pure (f x)

* Interchange:

    > u <*> pure y = pure ($y) <*> u

* Composition:

    > (.) <$> u <*> v <*> w = u <*> (v <*> w)
-}
apS :: Selective f => f (a -> b) -> f a -> f b
apS f x = select (Left <$> f) ((&) <$> x)

-- | One can easily implement a monadic 'selectM' that satisfies the laws,
-- hence any 'Monad' is 'Selective'.
selectM :: Monad f => f (Either a b) -> f (a -> b) -> f b
selectM x y = x >>= \case Left  a -> ($a) <$> y -- execute y
                          Right b -> pure b     -- skip y

-- Many useful 'Monad' combinators can be implemented with 'Selective'

-- | Branch on a Boolean value, skipping unnecessary effects.
ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS x t e = branch (bool (Right ()) (Left ()) <$> x) (const <$> t) (const <$> e)

-- Implementation used in the paper:
-- ifS x t e = branch selector (fmap const t) (fmap const e)
--   where
--     selector = bool (Right ()) (Left ()) <$> x -- NB: convert True to Left ()

-- | Eliminate a specified value @a@ from @f (Either a b)@ by replacing it
-- with a given @f b@.
eliminate :: (Eq a, Selective f) => a -> f b -> f (Either a b) -> f (Either a b)
eliminate x fb fa = select (match x <$> fa) (const . Right <$> fb)
  where
    match _ (Right y) = Right (Right y)
    match x (Left  y) = if x == y then Left () else Right (Left y)

-- | A list of values, equipped with a fast membership test.
data Cases a = Cases [a] (a -> Bool)

-- | The list of all possible values of an enumerable data type.
casesEnum :: (Bounded a, Enum a) => Cases a
casesEnum = Cases [minBound..maxBound] (const True)

-- | Embed a list of values into 'Cases' using the trivial but slow membership
-- test based on 'elem'.
cases :: Eq a => [a] -> Cases a
cases as = Cases as (`elem` as)

-- | Eliminate all specified values @a@ from @f (Either a b)@ by replacing each
-- of them with a given @f a@.
matchS :: (Eq a, Selective f) => Cases a -> f a -> (a -> f b) -> f (Either a b)
matchS (Cases cs _) x f = foldr (\c -> eliminate c (f c)) (Left <$> x) cs

-- | Eliminate all specified values @a@ from @f (Either a b)@ by replacing each
-- of them with a given @f a@.
matchM :: Monad m => Cases a -> m a -> (a -> m b) -> m (Either a b)
matchM (Cases _ p) mx f = do
    x <- mx
    if p x then Right <$> f x else pure (Left x)

-- TODO: Add a type-safe version based on @KnownNat@.
-- | A restricted version of monadic bind. Fails with an error if the 'Bounded'
-- and 'Enum' instances for @a@ do not cover all values of @a@.
bindS :: (Bounded a, Enum a, Eq a, Selective f) => f a -> (a -> f b) -> f b
bindS x f = fromRight <$> matchS casesEnum x f
  where
    fromRight (Right b) = b
    fromRight _ = error "Selective.bindS: incorrect Bounded and/or Enum instance"

-- | Conditionally perform an effect.
whenS :: Selective f => f Bool -> f () -> f ()
whenS x y = select (bool (Right ()) (Left ()) <$> x) (const <$> y)

-- Implementation used in the paper:
-- whenS x y = selector <*? effect
--   where
--     selector = bool (Right ()) (Left ()) <$> x -- NB: maps True to Left ()
--     effect   = const                     <$> y

-- | A lifted version of 'Data.Maybe.fromMaybe'.
fromMaybeS :: Selective f => f a -> f (Maybe a) -> f a
fromMaybeS fNothing fMaybe =
    select (toEither <$> fMaybe) (toUnitFunction <$> fNothing)
  where
    toEither :: Maybe a -> Either () a
    toEither Nothing  = Left ()
    toEither (Just a) = Right a
    toUnitFunction :: a -> () -> a
    toUnitFunction x () = x

-- | Return the first @Right@ value. If both are @Left@'s, accumulate errors.
orElse :: (Selective f, Semigroup e) => f (Either e a) -> f (Either e a) -> f (Either e a)
orElse x y = select (prepare <$> x) (combine <$> y)
  where
    prepare :: Either e a -> Either e (Either e a)
    prepare = fmap Right

    combine :: Semigroup e => Either e a -> e -> Either e a
    combine (Left ey) ex = Left (ex <> ey)
    combine (Right a) _  = Right a

-- | Accumulate the @Right@ values, or return the first @Left@.
andAlso :: (Selective f, Semigroup a) => f (Either e a) -> f (Either e a) -> f (Either e a)
andAlso x y = swapEither <$> orElse (swapEither <$> x) (swapEither <$> y)

-- | Swap @Left@ and @Right@.
swapEither :: Either a b -> Either b a
swapEither = either Right Left

-- | Keep checking an effectful condition while it holds.
whileS :: Selective f => f Bool -> f ()
whileS act = whenS act (whileS act)

-- | Keep running an effectful computation until it returns a @Right@ value,
-- collecting the @Left@'s using a supplied @Monoid@ instance.
untilRight :: (Monoid a, Selective f) => f (Either a b) -> f (a, b)
untilRight x = select y h
  where
    -- y :: f (Either a (a, b))
    y = fmap (mempty,) <$> x
    -- h :: f (a -> (a, b))
    h = (\(as, b) a -> (mappend a as, b)) <$> untilRight x

-- | A lifted version of lazy Boolean OR.
(<||>) :: Selective f => f Bool -> f Bool -> f Bool
a <||> b = ifS a (pure True) b

-- | A lifted version of lazy Boolean AND.
(<&&>) :: Selective f => f Bool -> f Bool -> f Bool
a <&&> b = ifS a b (pure False)

-- | A lifted version of 'any'. Retains the short-circuiting behaviour.
anyS :: Selective f => (a -> f Bool) -> [a] -> f Bool
anyS p = foldr ((<||>) . p) (pure False)

-- | A lifted version of 'all'. Retains the short-circuiting behaviour.
allS :: Selective f => (a -> f Bool) -> [a] -> f Bool
allS p = foldr ((<&&>) . p) (pure True)

-- | Generalised folding with the short-circuiting behaviour.
foldS :: (Selective f, Foldable t, Monoid a) => t (f (Either e a)) -> f (Either e a)
foldS = foldr andAlso (pure (Right mempty))

-- Instances

-- | Any applicative functor can be given a 'Selective' instance by defining
-- 'select' @=@ 'selectA'. This data type captures this pattern, so you can use
-- it in combination with the @DerivingVia@ extension as follows:
--
-- @
-- newtype Over m a = Over m
--     deriving (Functor, Applicative, Selective) via SelectA (Const m)
-- @
--
newtype SelectA f a = SelectA { getSelectA :: f a }
    deriving (Functor, Applicative)

instance Applicative f => Selective (SelectA f) where
    select = selectA

-- Note: Validation e a ~ Lift (Under e) a
instance Selective f => Selective (Lift f) where
    select (Pure (Right x)) _         = Pure x -- Lazy in the second argument
    select              x   (Pure  y) = either y id <$> x
    select (Pure (Left  x)) (Other y) = Other $ ($x) <$> y
    select (Other       x ) (Other y) = Other $   x  <*? y

-- | Any monad can be given a 'Selective' instance by defining
-- 'select' @=@ 'selectM'. This data type captures this pattern, so you can use
-- it in combination with the @DerivingVia@ extension as follows:
--
-- @
-- newtype V1 a = V1 a
--     deriving (Functor, Applicative, Selective, Monad) via SelectM Identity
-- @
--
newtype SelectM f a = SelectM { getSelectM :: f a }
    deriving (Functor, Applicative, Monad)

instance Monad f => Selective (SelectM f) where
    select = selectM

-- | Static analysis of selective functors with over-approximation.
newtype Over m a = Over { getOver :: m }
    deriving (Eq, Functor, Ord, Show)
    deriving Applicative via (Const m)

-- select = selectA
instance Monoid m => Selective (Over m) where
    select (Over x) (Over y) = Over (mappend x y)

-- | Static analysis of selective functors with under-approximation.
newtype Under m a = Under { getUnder :: m }
    deriving (Eq, Functor, Ord, Show, Foldable, Traversable)
    deriving Applicative via (Const m)

-- select = selectT
instance Monoid m => Selective (Under m) where
    select (Under m) _ = Under m

-- The 'Selective' 'ZipList' instance corresponds to the SIMT execution model.
-- Quoting https://en.wikipedia.org/wiki/Single_instruction,_multiple_threads:
--
-- "...to handle an IF-ELSE block where various threads of a processor execute
-- different paths, all threads must actually process both paths (as all threads
-- of a processor always execute in lock-step), but masking is used to disable
-- and enable the various threads as appropriate..."
instance Selective ZipList where select = selectA

-- | Selective instance for the standard applicative functor Validation. This is
-- a good example of a non-trivial selective functor which is not a monad.
data Validation e a = Failure e | Success a deriving (Eq, Functor, Ord, Show)

instance Semigroup e => Applicative (Validation e) where
    pure = Success
    Failure e1 <*> Failure e2 = Failure (e1 <> e2)
    Failure e1 <*> Success _  = Failure e1
    Success _  <*> Failure e2 = Failure e2
    Success f  <*> Success a  = Success (f a)

instance Semigroup e => Selective (Validation e) where
    select (Success (Left  a)) f = ($a) <$> f
    select (Success (Right b)) _ = Success b
    select (Failure e        ) _ = Failure e

instance (Selective f, Selective g) => Selective (Product f g) where
    select (Pair fx gx) (Pair fy gy) = Pair (select fx fy) (select gx gy)

instance Selective f => Selective (IdentityT f) where
    select (IdentityT x) (IdentityT y) = IdentityT (select x y)

instance Selective f => Selective (ReaderT env f) where
    select (ReaderT x) (ReaderT y) = ReaderT $ \env -> select (x env) (y env)

distributeEither :: (Either a b, w) -> Either (a, w) (b, w)
distributeEither (Left  a, w) = Left  (a, w)
distributeEither (Right b, w) = Right (b, w)

distributeFunction :: Monoid w => (a -> b, w) -> (a, w) -> (b, w)
distributeFunction (f, wf) (x, wx) = (f x, mappend wx wf)

instance (Monoid w, Selective f) => Selective (WriterT w f) where
    select (WriterT x) (WriterT f) =
        WriterT $ select (distributeEither <$> x) (distributeFunction <$> f)

instance (Monoid w, Selective f) => Selective (S.WriterT w f) where
    select (S.WriterT x) (S.WriterT f) =
        S.WriterT $ select (distributeEither <$> x) (distributeFunction <$> f)

-- TODO: Is this a useful instance? Note that composition of 'Alternative'
-- requires @f@ to be 'Alternative', and @g@ to be 'Applicative', which is
-- opposite to what we have here:
--
-- instance (Alternative f, Applicative g) => Alternative (Compose f g) ...
--
instance (Applicative f, Selective g) => Selective (Compose f g) where
    select (Compose x) (Compose y) = Compose (select <$> x <*> y)

{- Here is why composing selective functors is tricky.

Consider @Compose Maybe IO@. The only sensible implementation is:

> select :: Maybe (IO (Either a b)) -> Maybe (IO (a -> b)) -> Maybe (IO b)
> select Nothing  _        = Nothing
> select (Just x) (Just y) = Just (select x y)
> select (Just x) Nothing  = Nothing -- Can't use Just: we don't have @a -> b@!

In other words, we have to be 'Applicative' on the outside functor 'Maybe',
because there is no way to peek inside 'IO', which forces us to statically
choose between 'Just', which doesn't work since we have no function @a -> b@,
and 'Nothing' which corresponds to the behaviour of 'selectA'.

-}

-- Monad instances

-- As a quick experiment, try: ifS (pure True) (print 1) (print 2)
instance Selective IO where select = selectM

-- And... we need to write a lot more instances
instance             Selective []         where select = selectM
instance Monoid a => Selective ((,) a)    where select = selectM
instance             Selective ((->) a)   where select = selectM
instance             Selective (Either e) where select = selectM
instance             Selective Identity   where select = selectM
instance             Selective Maybe      where select = selectM
instance             Selective NonEmpty   where select = selectM
instance             Selective Proxy      where select = selectM
instance             Selective (ST s)     where select = selectM
instance             Selective STM        where select = selectM

instance                        Selective (ContT      r m) where select = selectM
instance            Monad m  => Selective (MaybeT       m) where select = selectM
instance (Monoid w, Monad m) => Selective (RWST   r w s m) where select = selectM
instance (Monoid w, Monad m) => Selective (S.RWST r w s m) where select = selectM
instance            Monad m  => Selective (StateT     s m) where select = selectM
instance            Monad m  => Selective (S.StateT   s m) where select = selectM

------------------------------------ Arrows ------------------------------------
-- See the following standard definitions in "Control.Arrow".
-- newtype ArrowMonad a o = ArrowMonad (a () o)
-- instance Arrow a => Functor (ArrowMonad a)
-- instance Arrow a => Applicative (ArrowMonad a)

instance ArrowChoice a => Selective (ArrowMonad a) where
    select (ArrowMonad x) y = ArrowMonad $ x >>> (toArrow y ||| returnA)

toArrow :: Arrow a => ArrowMonad a (i -> o) -> a i o
toArrow (ArrowMonad f) = arr ((),) >>> first f >>> arr (uncurry ($))

------------------------------ ComposeTraversable ------------------------------
-- | Composition of a selective functor @f@ and an applicative traversable
-- functor @g@.
newtype ComposeTraversable f g a = ComposeTraversable (f (g a))
    deriving (Functor, Applicative) via Compose f g

instance (Selective f, Applicative g, Traversable g) => Selective (ComposeTraversable f g) where
    select (ComposeTraversable x) (ComposeTraversable f) = ComposeTraversable $
        select (prepare <$> x) (combine <$> f)
      where
        prepare :: Traversable g => g (Either a b) -> Either a (g b)
        prepare = sequenceA

        combine :: Traversable g => g (a -> b) -> a -> g b
        combine = sequenceA

--------------------------------- ComposeEither --------------------------------
-- | Composition of a selective functor @f@ with the 'Either' monad.
newtype ComposeEither f e a = ComposeEither (f (Either e a))
    deriving Functor via Compose f (Either e)
    deriving Selective via ComposeTraversable f (Either e)

instance Selective f => Applicative (ComposeEither f e) where
    pure = ComposeEither . pure . Right

    ComposeEither f <*> ComposeEither a = ComposeEither $
        select (prepare <$> f) (combine <$> a)
      where
        prepare :: Either e (a -> b) -> Either (a -> b) (Either e b)
        prepare = either (Right . Left) Left

        combine :: Either e a -> (a -> b) -> Either e b
        combine = flip fmap

---------------------------------- Alternative ---------------------------------
instance (Selective f, Monoid e) => Alternative (ComposeEither f e) where
    empty                               = ComposeEither (pure $ Left mempty)
    ComposeEither x <|> ComposeEither y = ComposeEither (x `orElse` y)

{- One could also try implementing 'select' via 'Alternative' as follows:

selectAlt :: Alternative f => f (Either a b) -> f (a -> b) -> f b
selectAlt x y = failIfLeft x <|> selectA x y
  where
    failIfLeft :: Alternative f => f (Either a b) -> f b
    failIfLeft = undefined

This has two issues:

1) A generic 'failIfLeft' if not possible, although many actual instances should
   be able to implement it.

2) More importantly, this requires duplication of work: if we failed because we
   happened to parse a 'Left' value in the first parser, then we need to rerun
   it, obtain a 'Left' once again, and then execute the second parser. Again, a
   specific instance may be able to cache the result and reuse it without
   duplicating any work, but this does not seem to be possible to achieve
   generically for any Alternative.

-}
