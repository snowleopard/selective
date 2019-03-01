{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Selective.Example.ISA.Types where

import Prelude hiding (read)
import Data.Word (Word8)
import Data.Functor (void)
import Data.Int (Int8)
import Control.Selective
import Control.Selective.Free.Rigid

fromBool :: Num a => Bool -> a
fromBool True  = 1
fromBool False = 0
-- fromBool = bool 0 1

--------------------------------------------------------------------------------
-------- Types -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- | The ISA operates signed 16-bit words
type Value = Int8

-- | The ISA has 4 registers
data Register = R0 | R1 | R2 | R3
    deriving (Show, Eq, Ord)

r0, r1, r2, r3 :: Register
r0 = R0
r1 = R1
r2 = R2
r3 = R3

-- | The address space is indexed by one byte
type Address = Word8

-- | The ISA has two flags
data Flag = Zero     -- ^ tracks if the result of the last arithmetical operation was zero
          | Overflow -- ^ tracks integer overflow
          | Halted
    deriving (Show, Eq, Ord)

-- | Address in the program memory
type InstructionAddress = Value

-- | Index the locations of the ISA
data Key = Reg  Register
         | Cell Address
         | Flag Flag
         | PC
    deriving (Eq)

instance Show Key where
    show (Reg r )    = show r
    show (Cell addr) = show addr
    show (Flag f)    = show f
    show PC          = "PC"

data RW a = Read  Key             (Value -> a)
          | Write Key (ISA Value) (Value -> a)
    deriving Functor

instance Show a => Show (RW a) where
    show (Read  k _)   = "Read "  ++ show k
    show (Write k (Pure v) _) = "Write " ++ show k ++ " " ++ show v
    show (Write k _        _) = "Write " ++ show k

type ISA a = Select RW a

read :: Key -> ISA Value
read k = liftSelect (Read k id)

write :: Key -> ISA Value -> ISA Value
write k p = liftSelect (Write k p id)

-- | Interpret 'Read' and 'Write' commands in the 'Over' selective functor
inOver :: RW a -> Over [RW ()] b
inOver (Read  k _   ) = Over [void $ Read k (const ())]
inOver (Write k fv _) = void (runSelect inOver fv) *>
                        Over [Write k fv (const ())]

-- | Get effects of an ISA semantics computation
getEffectsISA :: ISA a -> [RW ()]
getEffectsISA = getOver . runSelect inOver
