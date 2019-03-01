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
import Data.List.NonEmpty (NonEmpty (..), fromList, toList)
import Control.Selective
import Control.Selective.Free.Rigid
import Control.Selective.Free.Examples.ISA.Types
import Control.Selective.Free.Examples.ISA.Instruction
import Control.Selective.Free.Examples.ISA.Simulate

addProgram :: Program
addProgram = fromList $ zip [0..]
    [Add R0 1]

addGraph :: IO ()
addGraph = writeFile "add.dot" $
    drawGraph (programGraph (toList addProgram))

jumpZeroProgram :: Program
jumpZeroProgram = fromList $ zip [0..]
    [JumpZero 42]

jumpZeroGraph :: IO ()
jumpZeroGraph = writeFile "jumpZero.dot" $
    drawGraph (programGraph (toList jumpZeroProgram))

addAndJump :: Program
addAndJump = fromList $ zip [0..]
    [ Add R0 1
    , JumpZero 2
    ]

addAndJumpSemantics :: ISA Value
addAndJumpSemantics =
    addOverflow R0 1 *>
    jumpZero 2

addAndJumpGraph :: IO ()
addAndJumpGraph = writeFile "addAndJump.dot" $
    drawGraph (programGraph (toList addAndJump))

notEqual :: Program
notEqual = fromList $ zip [0..]
    [ Load R0 0
    , Sub R0 1
    , JumpZero 1
    , Set R1 1
    , Halt
    ]

notEqualGraph :: IO ()
notEqualGraph = writeFile "notEqual.dot" $
    drawGraph (programGraph (toList notEqual))

notEqualSemantics :: ISA Value
notEqualSemantics =
    load R0 0 *>
    sub R0 1 *>
    jumpZero 1 *>
    set R1 1 *>
    halt

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

gcdGraph :: IO ()
gcdGraph = writeFile "gcd.dot" $
    drawGraph (programGraph (toList gcdProgram))

gcdState :: Value -> Value -> ISAState
gcdState x y = boot gcdProgram (initialiseMemory [(0, x), (1, y)])