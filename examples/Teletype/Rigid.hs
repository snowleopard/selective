{-# LANGUAGE DeriveFunctor, FlexibleInstances, GADTs #-}
module Teletype.Rigid where

import Prelude hiding (getLine, putStrLn)
import qualified Prelude as IO
import qualified Control.Monad as IO
import Control.Selective
import Control.Selective.Rigid.Free

-- See Section 5.2 of the paper: https://dl.acm.org/doi/10.1145/3341694.

-- | The classic @Teletype@ base functor.
data TeletypeF a = Read (String -> a) | Write String a deriving Functor

instance Eq (TeletypeF ()) where
    Read  _    == Read  _    = True
    Write x () == Write y () = x == y
    _ == _ = False

instance Show (TeletypeF a) where
    show (Read _)    = "Read"
    show (Write s _) = "Write " ++ show s

-- | Interpret 'TeletypeF' commands as 'IO' actions.
toIO :: TeletypeF a -> IO a
toIO (Read f)    = f <$> IO.getLine
toIO (Write s a) = a <$  IO.putStrLn s

-- | A Teletype program is a free selective functor on top of the base functor
-- 'TeletypeF'.
type Teletype a = Select TeletypeF a

-- | A convenient alias for reading a string.
getLine :: Teletype String
getLine = liftSelect (Read id)

-- | A convenient alias for writing a string.
putStrLn :: String -> Teletype ()
putStrLn s = liftSelect (Write s ())

-- | The ping-pong example from the introduction section of the paper
-- implemented using free selective functors.
--
-- @
-- > getEffects pingPongS
-- [Read,Write "pong"]
-- @
--
-- If can also be executed in IO:
--
-- @
-- > runSelect toIO pingPongS
-- hello
-- > runSelect toIO pingPongS
-- ping
-- pong
-- @
pingPongS :: Teletype ()
pingPongS = whenS (fmap ("ping"==) getLine) (putStrLn "pong")

------------------------------- Ping-pong example ------------------------------
-- | Monadic ping-pong, which has the desired behaviour, but cannot be
-- statically analysed.
pingPongM :: IO ()
pingPongM = IO.getLine >>= \s -> IO.when (s == "ping") (IO.putStrLn "pong")

-- | Applicative ping-pong, which always executes both effect, but can be
-- statically analysed.
pingPongA :: IO ()
pingPongA = IO.getLine *> IO.putStrLn "pong"

-- | A monadic greeting. Cannot be implemented using selective functors.
greeting :: IO ()
greeting = IO.getLine >>= \name -> IO.putStrLn ("Hello, " ++ name)
