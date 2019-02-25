{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Control.Selective.Free.Examples.ISA.Instruction where

import Prelude hiding (div, mod, read)
import qualified Prelude (div, mod)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty (..), fromList)
import Data.Functor (void)
-- import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Control.Selective
import Control.Selective.Free.Rigid
import Algebra.Graph
import Algebra.Graph.Export.Dot
import Control.Selective.Free.Examples.ISA.Types

--------------------------------------------------------------------------------
-------- Instructions ----------------------------------------------------------
--------------------------------------------------------------------------------

data Instruction where
  Halt     :: Instruction
  Load     :: Register -> Address -> Instruction
  Set      :: Register -> Value -> Instruction
  Store    :: Register -> Address -> Instruction
  Add      :: Register -> Address -> Instruction
  Sub      :: Register -> Address -> Instruction
  Mul      :: Register -> Address -> Instruction
  Div      :: Register -> Address -> Instruction
  Mod      :: Register -> Address -> Instruction
  Abs      :: Register -> Instruction
  Jump     :: Value -> Instruction
  JumpZero :: Value -> Instruction
  LoadMI   :: Register -> Address -> Instruction

deriving instance Show Instruction

type Program = NonEmpty (InstructionAddress, Instruction)

semantics :: Instruction -> ISA Value
semantics i = case i of
    Halt            -> halt
    Load reg addr   -> load reg addr
    LoadMI reg addr -> undefined -- loadMI reg addr
    Set reg val     -> set reg val
    Store reg addr  -> store reg addr
    Add reg1 addr   -> addOverflow reg1 addr
    Sub reg1 addr   -> sub reg1 addr
    Mul reg addr    -> mul reg addr
    Div reg addr    -> div reg addr
    Mod reg addr    -> mod reg addr
    Abs reg         -> undefined -- abs (Register reg)
    Jump simm8      -> jump simm8
    JumpZero simm8  -> jumpZero simm8

blockSemantics :: NonEmpty Instruction -> ISA Value
blockSemantics is =
    let meanings = fmap semantics is
    in foldl (*>) (NonEmpty.head meanings) (NonEmpty.tail meanings)

-------------
-- Halt -----
-------------

halt :: ISA Value
halt = write (F Halted) (pure 1)

------------
-- Set -----
------------

set :: Register -> Value -> ISA Value
set reg = write (Reg reg) . pure

-------------
-- Load -----
-------------

load :: Register -> Address -> ISA Value
load reg addr = write (Reg reg) (read (Mem addr))

--------------
-- Store -----
--------------

store :: Register -> Address -> ISA Value
store reg addr = write (Mem addr) (read (Reg reg))

------------
-- Add -----
------------

-- | Read the values of the variables "x" and "y" and write the sum into the variable "z".
--   If the sum is zero, write 1 into the variable "zero", otherwise put 0 there.
--
--   This implementation looks intuitive, but it is wrong, since the two write operations
--   can be considered independent and the effects required for computing the sum, i.e.
--   'read "x" <*> read "y"' will be executed twice. Consequently:
--   * the value written into the "z" variable is not guaranteed to be the same as the one which was
--     compared to zero,
--   * the static analysis of the computations reports more dependencies then one might have
--     naively expected
--
--     > getEffects addNaive
--     [Read R0,Read 0,Write Zero,Read R0,Read 0,Write R0]
--
--     Here, the two instances of 'sum' cause the duplication of 'Read R0' and 'Read 0' effects.
addNaive :: Register -> Address -> ISA Value
addNaive reg addr =
    let sum    = (+)  <$> read (Reg reg) <*> read (Mem addr)
        isZero = (==) <$> sum            <*> pure 0
    in write (F Zero) (ifS isZero (pure 1) (pure 0))
       *> write (Reg reg) sum

-- | This implementations of 'add' executes the effects associated with the 'sum' value only once and
--   then wires the pure value into the computations which require it without triggering the effects again.
--
--   > analyse add
--   ([],Left (W "zero" :| [W "z",R "y",R "x"]))
--
add :: Register -> Address -> ISA Value
add reg addr =
    let x = read (Reg reg)
        y = read (Mem addr)
        sum = (+) <$> x <*> y
        isZero = (==) <$> pure 0 <*> write (Reg reg) sum
    in write (F Zero) (fromBool <$> isZero)

-- -- | This is a fully inlined version of 'add'
-- addNormalForm :: ISA Value
-- addNormalForm =
--     write "zero" (ifS ((==) <$> pure 0 <*> write "z" ((+) <$> read "x" <*> read "y")) (pure 1) (pure 0))

-- addState :: Memory
-- addState =
--     Map.fromList [ ("x", 255)
--                  , ("y", 1)
--                  , ("zero", 0)
--                  , ("overflow", 0)
--                  , ("ic", 0)
--                  ]

-----------------
-- jumpZero -----
-----------------
jumpZero :: Value -> ISA Value
jumpZero offset =
    let pc       = read PC
        zeroSet  = (/=) <$> pure 0 <*> read (F Zero)
        -- modifyPC = void $ write PC (pure offset) -- (fmap (+ offset) pc)
        modifyPC = void $ write PC (fmap (+ offset) pc)
    in whenS zeroSet modifyPC *> pure offset

-- | Unconditional jump.
jump :: Value -> ISA Value
jump simm =
    write PC (fmap ((+) $ simm) (read PC))

-- jumpZeroMemory :: Map.Map Key Value
-- jumpZeroMemory =
--     Map.fromList [ ("ic", 0)
--                  , ("zero", 0)
--                  ]

-----------------------------------
-- Add with overflow tracking -----
-----------------------------------

{-  The following example will demonstrate how important it is to be aware of your effects.

    Problem: implement the semantics of add instruction which would calculate the sum and write it
    to the specified destination, update the 'zero' flag if the sum was zero, and also detect if
    integer overflow happened and update the 'overflow' flag accordingly.

    We'll take a look at two approaches that implement this semantics and see the crucial deference
    between them.
-}

-- | Add two values and detect integer overflow
-- The interesting bit here is the call to the 'willOverflowPure' function. Since the function is
-- pure, the call 'willOverflowPure <$> arg1 <*> arg2' triggers only one 'read' of 'arg1' and 'arg2',
-- even though we use the variables many times in the 'willOverflowPure' implementation.
--
--  > getEffects (addOverflow  R0 1)
--  [Read R0,Read 1,Write R0,Write Zero,Read R0,Read 1,Write Overflow]
--
-- Thus, 'willOverflowPure' might be though as a atomic microcommand in some sense.
addOverflow :: Register -> Address  -> ISA Value
addOverflow reg addr =
    let arg1     = read (Reg reg)
        arg2     = read (Mem addr)
        result   = (+)  <$> arg1   <*> arg2
        isZero   = (==) <$> pure 0 <*> write (Reg reg) result
        overflow = willOverflowPure <$> arg1 <*> arg2
    in write (F Zero)     (fromBool <$> isZero) *>
       write (F Overflow) (fromBool <$> overflow)

willOverflowPure :: Value -> Value -> Bool
willOverflowPure arg1 arg2 =
    let o1 = (>) arg2 0
        o2 = (>) arg1((-) maxBound arg2)
        o3 = (<) arg2 0
        o4 = (<) arg1((-) minBound arg2)
    in  (||) ((&&) o1 o2)
             ((&&) o3 o4)

-- | Add two values and detect integer overflow
--  In this implementations we take a different approach and, when implementing overflow detection,
--  lift all the pure operations into Applicative. This forces the semantics to read the input
--  variables more times than 'addOverflow' does (var1 3x times and addr 5x times)
--
--  > analyse (addOverflowNaive  "x" "y" "z")
--  ([],Left (W "overflow" :| [R "y",R "x",R "y",R "y",R "x",R "y",W "zero",W "z",R "y",R "x"]))
--
--  It is not clear at the moment what to do with that. Should we avoid this style? Or could it be
--  sometimes useful?
addOverflowNaive :: Register -> Address -> ISA Value
addOverflowNaive reg addr =
    let arg1   = read (Reg reg)
        arg2   = read (Mem addr)
        result = (+) <$> arg1 <*> arg2
        isZero = (==) <$> pure 0 <*> write (Reg reg) result
        overflow = willOverflow arg1 arg2
    in write (F Zero)     (fromBool <$> isZero) *>
       write (F Overflow) (fromBool <$> overflow)

-- add0 :: ISA (Value, Value, Bool, Bool, Value)
-- add0 = (\x y -> (x, y, True, True, 0)) <$> read (Reg R0) <*> read (Mem 1)

-- add1 :: ISA (Value, Value, Bool, Bool, Value)
-- add1 = (\(x, y, zero, overflow, sum) -> (x, y, x + y == 0, willOverflowPure x y, x + y)) <$> add0

-- add2 :: ISA Value
-- add2 = write (Reg R1) ((\(x, y, z, o, s) -> s) <$> add1) *>
--        write (F Zero) ((\(x, y, z, o, s) -> fromBool z) <$> add1)


willOverflow :: ISA Value -> ISA Value -> ISA Bool
willOverflow arg1 arg2 =
    let o1 = (>) <$> arg2 <*> pure 0
        o2 = (>) <$> arg1 <*> ((-) <$> pure maxBound <*> arg2)
        o3 = (<) <$> arg2 <*> pure 0
        o4 = (<) <$> arg1 <*> ((-) <$> pure minBound <*> arg2)
    in  (||) <$> ((&&) <$> o1 <*> o2)
             <*> ((&&) <$> o3 <*> o4)

----------------------------------------------------------------------------------------------------

-- | Subtraction
--   NOTE: currently always sets the 'Overflow' flag to zero
sub :: Register -> Address -> ISA Value
sub reg addr =
    let arg1     = read (Reg reg)
        arg2     = read (Mem addr)
        result   = (-)  <$> arg1   <*> arg2
        isZero   = (==) <$> pure 0 <*> write (Reg reg) result
    in write (F Zero)     (fromBool <$> isZero) *>
       write (F Overflow) (pure 0)

-- | Multiply a value from memory location to one in a register.
--   Applicative.
mul :: Register -> Address -> ISA Value
mul reg addr =
    let result = (*) <$> read (Reg reg) <*> read (Mem addr)
    in  write (F Zero) (fromBool . (== 0) <$> write (Reg reg) result)

div :: Register -> Address -> ISA Value
div reg addr =
    let result = Prelude.div <$> read (Reg reg) <*> read (Mem addr)
    in  write (F Zero) (fromBool . (== 0) <$> write (Reg reg) result)

mod :: Register -> Address -> ISA Value
mod reg addr =
    let result = Prelude.mod <$> read (Reg reg) <*> read (Mem addr)
    in  write (F Zero) (fromBool . (== 0) <$> write (Reg reg) result)

-- --------------------------------------------------------------------------------

partition :: [RW a] -> ([Key], [Key])
partition = foldl go ([], [])
    where go (accR, accW) = \case (Read  k _)   -> (k : accR, accW)
                                  (Write k _ _) -> (accR, k : accW)

-- | Compute static data flow graph of an instruction.
instructionGraph :: (InstructionAddress, Instruction)
                    -> Graph (Either Key (InstructionAddress, Instruction))
instructionGraph instrInfo@(_, instr) =
    let (ins, outs) = partition $ getEffects (semantics instr)
    in overlay (star (Right instrInfo) (map Left outs))
               (transpose $ star (Right instrInfo) (map Left ins))

-- | Compute static data flow graph of a program.
programGraph :: [(InstructionAddress, Instruction)]
                 -> Graph (Either Key (InstructionAddress, Instruction))
programGraph p = foldl go empty (map instructionGraph p)
    where go acc g = overlay acc g
--------------------------------------------------------------------------------

-- | Serialise data flow graph as a .dot string
-- drawGraph :: Graph (Either String (InstructionAddress, Instruction)) -> String
drawGraph :: Graph (Either Key (InstructionAddress, Instruction)) -> String
drawGraph g =
    let g' = stringifyVertex <$> g
        names = vertexSet g'
        style = defaultStyleViaShow
            { vertexName = \v -> "v" ++ show (fromJust $ Set.lookupIndex v names)
            , vertexAttributes = \x -> case x of
                Left  k -> [ "shape"  := "circle"
                           , "label"  := k ]
                Right i -> [ "shape" := "record"
                           , "label" := i ] }
    in export style g'
    where
        stringifyVertex :: Either Key (InstructionAddress, Instruction) ->
                           Either String String
        stringifyVertex (Left k)       = Left  (show k)
        stringifyVertex (Right (a, i)) = Right $ show a <> "|" <> show i