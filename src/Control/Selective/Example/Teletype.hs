{-# LANGUAGE DeriveFunctor, GADTs #-}
module Control.Selective.Example.Teletype where

import Prelude hiding (getLine, putStrLn)
import qualified Prelude (getLine, putStrLn)
import Control.Selective
import Control.Selective.Free.Rigid

data TeletypeF a = Get (String -> a)
                 | Put String a
    deriving Functor

instance Show (TeletypeF a) where
    show (Get _)   = "Get"
    show (Put s _) = "Put " ++ show s

-- | Interpret the 'TeletypeF' commands as IO actions
toIO :: TeletypeF a -> IO a
toIO (Get f)   = f <$> Prelude.getLine
toIO (Put s a) = a <$  Prelude.putStrLn s

-- | A Teletype program is a free Selective over the 'TeletypeF' functor
type Teletype a = Select TeletypeF a

getLine :: Teletype String
getLine = liftSelect (Get id)

putStrLn :: String -> Teletype ()
putStrLn s = liftSelect (Put s ())

-- | The example from the paper's intro. Implemented in terms of the free
--   selective, can now be statically analysed for effects:
--
--   > getEffects pingPongS
--   [Get,Put "pong"]
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
