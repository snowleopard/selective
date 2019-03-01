{-# LANGUAGE DeriveFunctor, GADTs #-}
module Control.Selective.Example.Teletype where

import Prelude hiding (getLine, putStrLn)
import qualified Prelude (getLine, putStrLn)
import Control.Selective
import Control.Selective.Free.Rigid

data TeletypeF a = Read (String -> a)
                 | Write String a
    deriving Functor

instance Show (TeletypeF a) where
    show (Read _)    = "Read"
    show (Write s _) = "Write " ++ show s

-- | Interpret the 'TeletypeF' commands as IO actions
toIO :: TeletypeF a -> IO a
toIO (Read f)    = f <$> Prelude.getLine
toIO (Write s a) = a <$  Prelude.putStrLn s

-- | A Teletype program is a free Selective over the 'TeletypeF' functor
type Teletype a = Select TeletypeF a

getLine :: Teletype String
getLine = liftSelect (Read id)

putStrLn :: String -> Teletype ()
putStrLn s = liftSelect (Write s ())

greeting :: IO ()
greeting = Prelude.getLine >>= \name -> Prelude.putStrLn ("Hello, " ++ name)

-- | The example from the paper's intro. Implemented in terms of the free
--   selective, can now be statically analysed for effects:
--
--   > getEffects pingPongS
--   [Read,Write "pong"]
--
--   We can also execute the program in IO:
--   > runSelect toIO pingPong
--   ping
--   pong
--
--   > runSelect toIO pingPong
--   bing
--   <no responce>
pingPongS :: Teletype ()
pingPongS = whenS (fmap ("ping"==) getLine) (putStrLn "pong")
