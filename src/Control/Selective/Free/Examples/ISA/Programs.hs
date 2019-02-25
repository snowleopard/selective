{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}



module Control.Selective.Free.Examples.ISA.Programs where

import Prelude hiding (mod, read)
import Data.List.NonEmpty (NonEmpty (..), fromList)
import Control.Selective
import Control.Selective.Free.Rigid
import Control.Selective.Free.Examples.ISA.Types
import Control.Selective.Free.Examples.ISA.Instruction
import Control.Selective.Free.Examples.ISA.Simulate

notEqual :: Program
notEqual = fromList $ zip [0..]
    [ Load R0 0
    , Sub R0 1
    , JumpZero 1
    , Set R1 1
    , Halt
    ]

notEqualState :: Value -> Value -> ISAState
notEqualState x y = boot notEqual (initialiseMemory [(0, x), (1, y), (2, 42)])

gcdProgram :: Program
gcdProgram = fromList $ zip [0..]
    -- # Find the greatest common divisor of values in memory locations 0 and 1,
    -- # put result to the register R1
    [ (Set R0 0)
    , (Store R0 255)
    , (Load R0 1)
    -- # Test register R0 for being zero by subtracting zero
    , (Sub R0 255)
    -- # Halt if register R0 contains zero, loop otherwise
    , (JumpZero 6)
    , (Load R0 0)
    , (Mod R0 1)
    , (Load R1 1)
    , (Store R0 1)
    , (Store R1 0)
    , (Jump (-8))
    , Halt
    ]

gcdState :: Value -> Value -> ISAState
gcdState x y = boot gcdProgram (initialiseMemory [(0, x), (1, y)])