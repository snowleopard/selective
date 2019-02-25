{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}

module Control.Selective.Free.Examples.PingPong where

import Prelude hiding (getLine, putStrLn)
import qualified Prelude (getLine, putStrLn)
import Control.Selective
import Control.Selective.Free

-- | The 'RW' (pronounced "Read-Write") functor is abstracts a key-value store.
data RW k v a = Read  k   (v -> a)
              -- ^ read a value 'v' associated to to the key 'k' and transform it to an 'a'.
              | Write k v (v -> a)
              -- ^ associate the value 'v' with the key 'k',
              --   then transform the 'v' to an 'a' and return it as a result
    deriving Functor

instance (Show k, Show v, Show a) => Show (RW k v a) where
    show (Read k _)    = "Read "  ++ show k
    show (Write k v _) = "Write " ++ show k ++ " " ++ show v

-- | A TeletypeF is an specialisation of the 'RW' with a singleton key datatype
--   and character strings as values
newtype TeletypeF a = TeletypeF { runTeletypeF :: RW () String a }
    deriving newtype Functor
    deriving Show via (RW () String a)


-- | Interpret the 'TeletypeF' commands as IO actions
inIO :: TeletypeF a -> IO a
inIO (TeletypeF (Read _ t))    = t <$> Prelude.getLine
inIO (TeletypeF (Write _ v t)) = t <$> (Prelude.putStrLn v *> pure v)

-- | A Teletype program is a free Selective over the 'TeletypeF' functor
type Teletype a = Select TeletypeF a

getLine :: Teletype String
getLine = liftSelect (TeletypeF $ Read () id)

putStrLn :: String -> Teletype ()
putStrLn v = liftSelect (TeletypeF $ Write () v (const ()))

-- | The example from the paper's intro. Implemented in terms of the free
--   selective, can now be statically analysed for necessary effects:
--
--   > analyse pingPong
--   ([],Left (Write () "pong" :| [Read ()]))
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

