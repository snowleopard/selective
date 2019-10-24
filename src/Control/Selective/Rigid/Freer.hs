{-# LANGUAGE DeriveFunctor, GADTs, RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Selective.Rigid.Freer
-- Copyright  : (c) Andrey Mokhov 2018-2019
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- This is a library for /selective applicative functors/, or just
-- /selective functors/ for short, an abstraction between applicative functors
-- and monads, introduced in this paper:
-- https://www.staff.ncl.ac.uk/andrey.mokhov/selective-functors.pdf.
--
-- This module defines /freer rigid selective functors/. Rigid selective
-- functors are those that satisfy the property @\<*\> = apS@. Compared to the
-- "free" construction from "Control.Selective.Rigid.Free", this "freer"
-- construction does not require the underlying base data type to be a functor.
--
-----------------------------------------------------------------------------
module Control.Selective.Rigid.Freer (
    -- * Free rigid selective functors
    Select (..), liftSelect,

    -- * Static analysis
    getPure, getEffects, getNecessaryEffect, runSelect, foldSelect,

    -- ** Analysis using 'Some'
    
    -- | Freer formulation is useful with GADTs, which aren't 'Functor's.
    --
    -- === __Examples__
    --
    -- >>> :set -XGADTs -XStandaloneDeriving
    -- 
    -- An interpreter of 'CMD's.
    -- We can flip different coins,
    -- and display strings.
    --
    -- >>> data CMD a where FlipCoin :: Int -> CMD Bool; Display :: String -> CMD ()
    -- 
    -- 'Show' instance:
    --
    -- >>> deriving instance Show (CMD a)
    -- >>> instance GShow CMD where gshowsPrec = showsPrec
    --
    -- Lifted commands
    --
    -- >>> let flipCoin n = liftSelect (FlipCoin n)
    -- >>> let display s  = liftSelect (Display s)
    --
    -- Next we can define a small program:
    --
    -- >>> let program = ifS (flipCoin 0) (display "Heads") (display "Tails")
    --
    -- This is program is clearly not pure:
    --
    -- >>> getPure program
    -- Nothing
    --
    -- The blocked action is unsurpringly a coin toss:
    --
    -- >>> getSomeNecessaryEffect program
    -- Just (Some (FlipCoin 0))
    --
    -- But we can also see all the effects the program may perform
    --
    -- >>> getEffectsSome program
    -- [Some (FlipCoin 0),Some (Display "Heads"),Some (Display "Tails")]
    --
    -- We can also flip two coins:
    --
    -- >>> let program2 = ifS (liftA2 xor (flipCoin 1) (flipCoin 2)) (display "Different") (display "Same")
    --
    -- This is an example where strict normal form trashes the analysys:
    -- @'FlipCoin' 2@ is also necessary, as we use (cleverly picked) 'xor'
    -- operation which cannot short-circuit.
    -- The 'getSomeNecessaryEffect' (and 'getNecessaryEffect')
    -- return at most one effect.
    --
    -- >>> getSomeNecessaryEffect program2
    -- Just (Some (FlipCoin 1))
    --
    -- We can also interpret the program, first we need to define a function
    -- for interpretting individual effects:
    --
    -- >>> :{
    -- cmd :: CMD a -> IO a
    -- cmd (FlipCoin n) = do
    --     x <- randomIO
    --     putStrLn $ "flip coin " ++ show n ++ ": " ++ show x
    --     return x
    -- cmd (Display s)  = putStrLn s
    -- :}
    --
    -- Then we can interpret complete program:
    --
    -- >>> runSelect cmd program2
    -- flip coin 1: True
    -- flip coin 2: False
    -- Different
    --
    getEffectsSome,
    getSomeNecessaryEffect,
    ) where

import Control.Selective
import Data.Bifunctor
import Data.Function
import Data.Functor
import Data.Some (Some, mkSome)
import Data.Monoid (First (..))

-- $setup
-- >>> import Data.GADT.Show
-- >>> import Control.Applicative (liftA2)
-- >>> import Data.Bits (xor)
--
-- deterministic "random" generator
--
-- >>> import Data.IORef
-- >>> ref <- newIORef True
-- >>> randomIO = atomicModifyIORef' ref (\x -> (not x, x))

-- Inspired by free applicative functors by Capriotti and Kaposi.
-- See: https://arxiv.org/pdf/1403.0749.pdf

-- Note: In the current implementation, 'fmap' and 'select' cost O(N), where N
-- is the number of effects. It is possible to improve this to O(1) by using the
-- idea developed for free applicative functors by Dave Menendez, see this blog
-- post: https://www.eyrie.org/~zednenem/2013/05/27/freeapp.
-- An example implementation can be found here:
-- http://hackage.haskell.org/package/free/docs/Control-Applicative-Free-Fast.html

-- | Free rigid selective functors.
data Select f a where
    Pure   :: a -> Select f a
    Select :: Select f (Either (x -> a) a) -> f x -> Select f a

-- TODO: Prove that this is a lawful 'Functor'.
instance Functor (Select f) where
    fmap f (Pure a)     = Pure (f a)
    fmap f (Select x y) = Select (bimap (f.) f <$> x) y -- O(N)

-- TODO: Prove that this is a lawful 'Applicative'.
instance Applicative (Select f) where
    pure  = Pure
    (<*>) = apS -- Rigid selective functors

-- TODO: Prove that this is a lawful 'Selective'.
instance Selective (Select f) where
    select = selectBy (first (&))
      where
        selectBy :: (a -> Either (b -> c) c) -> Select f a -> Select f b -> Select f c
        selectBy f x (Pure y)     = either ($y) id . f <$> x
        selectBy f x (Select y z) = Select (selectBy g x y) z -- O(N)
          where
            g a = case f a of Right c -> Right (Right c)
                              Left bc -> Left  (bimap (bc.) bc)

-- | Lift a functor into a free selective computation.
liftSelect :: f a -> Select f a
liftSelect f = Select (Pure (Left id)) f

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @Select f@ to @g@.
runSelect :: Selective g => (forall x. f x -> g x) -> Select f a -> g a
runSelect _ (Pure a)     = pure a
runSelect t (Select x y) = select (runSelect t x) ((&) <$> t y)

-- | Concatenate all effects of a free selective computation.
foldSelect :: Monoid m => (forall x. f x -> m) -> Select f a -> m
foldSelect f = getOver . runSelect (Over . f)

-- | Extract the resulting value if there are no necessary effects.
getPure :: Select f a -> Maybe a
getPure = runSelect (const Nothing)

-- | Collect all possible effects in the order they appear in a free selective
-- computation.
getEffects :: Functor f => Select f a -> [f ()]
getEffects = foldSelect (pure . void)

-- | Like 'getEffects' but not requiring @'Functor' f@.
getEffectsSome :: Select f a -> [Some f]
getEffectsSome = foldSelect (pure . mkSome)

-- | Extract the necessary effect from a free selective computation. Note: there
-- can be at most one effect that is statically guaranteed to be necessary.
getNecessaryEffect :: Functor f => Select f a -> Maybe (f ())
getNecessaryEffect = getFirst . foldSelect (First . Just . void)

-- | Like 'getNecessaryEffect' but not requiring @'Functor' f@.
getSomeNecessaryEffect :: Select f a -> Maybe (Some f)
getSomeNecessaryEffect = getFirst . foldSelect (First . Just . mkSome)
