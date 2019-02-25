{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}

module Control.Selective.Free.Examples.Teletype where

import Prelude hiding (getLine, putStrLn)
import qualified Prelude (getLine, putStrLn)
import Control.Selective
import Control.Selective.Free.Rigid

data TeletypeF a = GetLine (String -> a)
                 | PutLine String a
    deriving Functor

instance Show (TeletypeF a) where
    show (GetLine _)   = "GetLine"
    show (PutLine s _) = "PutLine " ++ s

-- | Interpret the 'TeletypeF' commands as IO actions
inIO :: TeletypeF a -> IO a
inIO (GetLine t)   = t <$> Prelude.getLine
inIO (PutLine s x) = Prelude.putStrLn s *> pure x

-- | A Teletype program is a free Selective over the 'TeletypeF' functor
type Teletype a = Select TeletypeF a

getLine :: Teletype String
getLine = liftSelect (GetLine id)

putStrLn :: String -> Teletype ()
putStrLn s = liftSelect (PutLine s ())

-- | The example from the paper's intro. Implemented in terms of the free
--   selective, can now be statically analysed for effects:
--
--   > getEffects pingPong
--   ([],Left (PutLine pong :| [GetLine]))
--
--   We can also run the program in IO:
--   > runSelect inIO pingPong
--   ping
--   pong
--
--   > runSelect inIO pingPong
--   bing
--   <no responce>
pingPong :: Teletype ()
pingPong = whenS (fmap (=="ping") getLine) (putStrLn "pong")
