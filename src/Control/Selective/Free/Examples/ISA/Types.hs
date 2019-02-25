{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Selective.Free.Examples.ISA.Types where

import Prelude hiding (read)
import Data.Either (partitionEithers)
import Data.Word (Word8)
import Data.Functor (void)
import Data.Int (Int16)
import Data.Functor (void)
import qualified Data.Map.Strict as Map
import Control.Selective
import Control.Selective.Free.Rigid

fromBool :: Num a => Bool -> a
fromBool True  = 1
fromBool False = 0

--------------------------------------------------------------------------------
-------- Types -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- | The ISA operates signed 16-bit words
type Value = Int16

-- | The ISA has 4 registers
data Register = R0 | R1 | R2 | R3
    deriving (Show, Eq, Ord)

r0, r1, r2, r3 :: Register
[r0, r1, r2, r3] = [R0, R1, R2, R3]
_ = undefined

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
data Key = Reg Register
         | Mem Address
         | F   Flag
         | PC
    deriving (Eq)

instance Show Key where
    show (Reg r )   = show r
    show (Mem addr) = show addr
    show (F   f)    = show f
    show PC         = "PC"

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

inOver :: RW a -> Over [RW ()] b
inOver (Read  k t   ) = Over [void $ Read k (const ())]
inOver (Write k fv t) = void (runSelect inOver fv) *>
                        Over [Write k fv (const ())]

getEffectsISA :: ISA a -> [RW ()]
getEffectsISA = getOver . runSelect inOver

