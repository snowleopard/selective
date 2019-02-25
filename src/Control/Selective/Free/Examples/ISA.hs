{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Selective.Free.Examples.ISA where

import Prelude hiding (read)
import Data.Word (Word8)
import Data.Int (Int16)
import Data.Functor (void)
import qualified Control.Monad.State as S
import Control.Selective
import Control.Selective.Free.Rigid
import qualified Data.Map.Strict as Map

-- | Hijack mtl's MonadState constraint to include Selective
type MonadState s m = (Selective m, S.MonadState s m)

fromBool :: Num a => Bool -> a
fromBool True  = 1
fromBool False = 0

--------------------------------------------------------------------------------
-------- Types -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- | The ISA operates signed 16-bit words
type Value = Int16

-- | The ISA has 4 registers
data Reg = R1 | R2 | R3 | R4
    deriving (Show, Eq, Ord)

r0, r1, r2, r3 :: Key
[r0, r1, r2, r3] = map Register [R1, R2, R3, R4]
_ = undefined

type RegisterBank = Map.Map Reg Value

-- | The address space is indexed by one byte
type Address = Word8

-- | We model memory as a map from bytes to signed 16-bit words
type Memory = Map.Map Address Value

-- | The ISA has two flags
data F = Zero     -- ^ tracks if the result of the last arithmetical operation was zero
       | Overflow -- ^ tracks integer overflow
    deriving (Show, Eq, Ord)

type Flags = Map.Map F Value

-- | Address in the program memory
type InstructionAddress = Value

-- data Key v where
--     Register :: Reg -> Key Value              -- ^ Refer to a register
--     Memory   :: Address  -> Key Value         -- ^ Refer to a memory location
--     Flag     :: F  -> Key Bool                -- ^ Refer to a flag
--     PC       :: Key InstructionAddress -- ^ Refer to the program counter

data Key =
    Register Reg
    | Memory Address
    | Flag   F
    | PC

instance Show Key where
    show (Register r ) = show r
    show (Memory addr) = show addr
    show (Flag   f)    = show f
    show PC            = "PC"

deriving instance Eq Key

data ISAState = ISAState { registers :: RegisterBank
                         , memory    :: Memory
                         , pc        :: InstructionAddress
                         , flags     :: Flags
                         }

data RW a = R Key             (Value -> a)
          | W Key (ISA Value) (Value -> a)
    deriving Functor

type ISA a = Select RW a

instance Show a => Show (RW a) where
    show (R k _)   = "Read "  ++ show k
    show (W k (Pure v) _) = "Write " ++ show k ++ " " ++ show v
    show (W k _        _) = "Write " ++ show k
    -- show (W k (Select f v)        _) = "Write " ++ show k ++ " unknown"
    -- show (W k (Select (Pure (Left x)) f)        _) = "Write " ++ show k ++ " " -- ++ show x

-- | Interpret the internal ISA effect in 'MonadState'
toState :: MonadState ISAState m => RW a -> m a
toState (R k t) = t <$> case k of
    Register r  -> (Map.!) <$> (registers <$> S.get) <*> pure r
    Memory addr -> (Map.!) <$> (memory    <$> S.get) <*> pure addr
    Flag f      -> (Map.!) <$> (flags     <$> S.get) <*> pure f
    PC          -> pc <$> S.get
toState (W k p t) = case k of
    Register r  -> do v <- runSelect toState p
                      let regs' s = Map.insert r v (registers s)
                      S.state (\s -> (t v, s {registers = regs' s}))
    Memory addr -> do v <- runSelect toState p
                      let mem' s = Map.insert addr v (memory s)
                      S.state (\s -> (t v, s {memory = mem' s}))
    Flag f      -> do v <- runSelect toState p
                      let flags' s = Map.insert f v (flags s)
                      S.state (\s -> (t v, s {flags = flags' s}))
    PC          -> error "toState: Can't write the Program Counter (PC)"


-- | Interpret a 'Program' in the state monad
runProgramState :: ISA a -> ISAState -> (a, ISAState)
runProgramState f s = S.runState (runSelect toState f) s

read :: Key -> ISA Value
read k = liftSelect (R k id)

write :: Key -> ISA Value -> ISA Value
write k p = p *> liftSelect (W k p id)

-- --------------------------------------------------------------------------------
-- -------- Instructions ----------------------------------------------------------
-- --------------------------------------------------------------------------------

runProgram :: ISA a -> ISAState -> (a, ISAState)
runProgram prog memory = runProgramState prog memory

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
--     > analyse addNaive
--     ([],Left (W "z" :| [R "y",R "x",W "zero",R "y",R "x"]))
--
--     Here, the two instances of 'sum' cause the duplication of 'R "x"' and R '"y"' effects.
addNaive :: Key -> Key -> Key -> ISA Value
addNaive reg1 reg2 reg3 =
    let sum = (+) <$> read reg1 <*> read reg2
        isZero = (==) <$> sum <*> pure 0
    in write (Flag Zero) (ifS isZero (pure 1) (pure 0))
       *> write reg3 sum

-- | This implementations of 'add' executes the effects associated with the 'sum' value only once and
--   then wires the pure value into the computations which require it without triggering the effects again.
--
--   > analyse add
--   ([],Left (W "zero" :| [W "z",R "y",R "x"]))
--
add :: Key -> Key -> Key -> ISA Value
add reg1 reg2 reg3 =
    let x = read reg1
        y = read reg2
        sum = (+) <$> x <*> y
        isZero = (==) <$> pure 0 <*> write reg3 sum
    in write (Flag Zero) (fromBool <$> isZero)

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
jumpZero :: Value -> ISA ()
jumpZero offset =
    let pc       = read PC
        zeroSet  = (/=) <$> pure 0 <*> read (Flag Zero)
        -- modifyPC = void $ write PC (pure offset) -- (fmap (+ offset) pc)
        modifyPC = void $ write PC (fmap (+ offset) pc)
    in whenS zeroSet modifyPC

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
--  > analyse (addOverflow  "x" "y" "z")
--  ([],Left (W "overflow" :| [R "y",R "x",W "zero",W "z",R "y",R "x"]))
--
-- Thus, 'willOverflowPure' might be though as a atomic microcommand in some sense.
addOverflow :: Key -> Key -> Key -> ISA Value
addOverflow var1 var2 dest =
    let arg1     = read var1
        arg2     = read var2
        result   = (+)  <$> arg1   <*> arg2
        isZero   = (==) <$> pure 0 <*> write dest result
        overflow = willOverflowPure <$> arg1 <*> arg2
    in write (Flag Zero)     (fromBool <$> isZero) *>
       write (Flag Overflow) (fromBool <$> overflow)

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
--  variables more times than 'addOverflow' does (var1 3x times and var2 5x times)
--
--  > analyse (addOverflowNaive  "x" "y" "z")
--  ([],Left (W "overflow" :| [R "y",R "x",R "y",R "y",R "x",R "y",W "zero",W "z",R "y",R "x"]))
--
--  It is not clear at the moment what to do with that. Should we avoid this style? Or could it be
--  sometimes useful?
addOverflowNaive :: Key -> Key -> Key -> ISA Value
addOverflowNaive var1 var2 dest =
    let arg1   = read var1
        arg2   = read var2
        result = (+) <$> arg1 <*> arg2
        isZero = (==) <$> pure 0 <*> write dest result
        overflow = willOverflow arg1 arg2
    in write (Flag Zero)     (fromBool <$> isZero) *>
       write (Flag Overflow) (fromBool <$> overflow)

willOverflow :: ISA Value -> ISA Value -> ISA Bool
willOverflow arg1 arg2 =
    let o1 = (>) <$> arg2 <*> pure 0
        o2 = (>) <$> arg1 <*> ((-) <$> pure maxBound <*> arg2)
        o3 = (<) <$> arg2 <*> pure 0
        o4 = (<) <$> arg1 <*> ((-) <$> pure minBound <*> arg2)
    in  (||) <$> ((&&) <$> o1 <*> o2)
             <*> ((&&) <$> o3 <*> o4)

----------------------------------------------------------------------------------------------------
