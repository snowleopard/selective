{-# LANGUAGE ConstraintKinds, DeriveFunctor
             , LambdaCase, FlexibleContexts, FlexibleInstances, GADTs #-}
module Processor where

import Control.Selective
import Control.Selective.Free.Rigid
import Data.Functor
import Data.Int (Int16)
import Data.Word (Word8)
import Data.Map.Strict (Map)
import Prelude hiding (read, log)

import qualified Control.Monad.State as S
import qualified Data.Map.Strict     as Map

-- See Section 5.3 of the paper:
-- https://www.staff.ncl.ac.uk/andrey.mokhov/selective-functors.pdf
-- Note that we have changed the naming.

-- | Hijack @mtl@'s 'MonadState' constraint to include Selective.
type MonadState s m = (Selective m, S.MonadState s m)

-- | Convert a 'Bool' to @0@ or @1@.
fromBool :: Num a => Bool -> a
fromBool True  = 1
fromBool False = 0

--------------------------------------------------------------------------------
-------- Types -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- | All values are signed 16-bit words.
type Value = Int16

-- | The processor has four registers.
data Reg = R0 | R1 | R2 | R3 deriving (Show, Eq, Ord)

r0, r1, r2, r3 :: Key
r0 = Reg R0
r1 = Reg R1
r2 = Reg R2
r3 = Reg R3

-- | The register bank maps registers to values.
type RegisterBank = Map Reg Value

-- | The address space is indexed by one byte.
type Address = Word8

-- | The memory maps addresses to signed 16-bit words.
type Memory = Map.Map Address Value

-- | The processor has two status flags.
data Flag = Zero     -- ^ tracks if the result of the last arithmetical operation was zero
          | Overflow -- ^ tracks integer overflow
    deriving (Show, Eq, Ord)

-- | A flag assignment.
type Flags = Map.Map Flag Value

-- | Address in the program memory.
type InstructionAddress = Value

-- | A program execution log entry, recording either a read from a key and the
-- obtained value, or a write to a key, along with the written value.
data LogEntry k v where
    ReadEntry  :: k -> v -> LogEntry k v
    WriteEntry :: k -> v -> LogEntry k v

-- | A log is a sequence of log entries, in the execution order.
type Log k v = [LogEntry k v]

-- | The complete processor state.
data State = State { registers :: RegisterBank
                   , memory    :: Memory
                   , pc        :: InstructionAddress
                   , flags     :: Flags
                   , log       :: Log Key Value}

-- | Various elements of the processor state.
data Key = Reg Reg | Cell Address | Flag Flag | PC deriving Eq

instance Show Key where
    show (Reg r)  = show r
    show (Cell a) = show a
    show (Flag f) = show f
    show PC       = "PC"

-- | The base functor for mutable processor state.
data RW a = R Key                 (Value -> a)
          | W Key (Program Value) (Value -> a)
    deriving Functor

-- | A program is a free selective on top of the 'RW' base functor.
type Program a = Select RW a

instance Show (RW a) where
    show (R k          _) = "Read "  ++ show k
    show (W k (Pure v) _) = "Write " ++ show k ++ " " ++ show v
    show (W k _        _) = "Write " ++ show k

logEntry :: MonadState State m => LogEntry Key Value -> m ()
logEntry item = S.modify $ \s ->
    s {log = log s ++ [item] }

-- | Interpret the base functor in a 'MonadState'.
toState :: MonadState State m => RW a -> m a
toState = \case
    (R k t) -> do
        v <- case k of
                   Reg  r    -> (Map.! r   ) <$> S.gets registers
                   Cell addr -> (Map.! addr) <$> S.gets memory
                   Flag f    -> (Map.! f   ) <$> S.gets flags
                   PC        -> pc <$> S.get
        logEntry (ReadEntry k v)
        pure (t v)
    (W k p t) -> do
        v <- runSelect toState p
        logEntry (WriteEntry k v)
        case k of
            Reg r     -> let regs' s = Map.insert r v (registers s)
                         in  S.state (\s -> (t v, s {registers = regs' s}))
            Cell addr -> let mem' s = Map.insert addr v (memory s)
                         in S.state (\s -> (t v, s {memory = mem' s}))
            Flag f    -> let flags' s = Map.insert f v (flags s)
                         in S.state (\s -> (t v, s {flags = flags' s}))
            PC        -> S.state (\s -> (t v, s {pc = v}))

-- | Interpret a program as a state trasformer.
runProgramState :: Program a -> State -> (a, State)
runProgramState f = S.runState (runSelect toState f)

-- | Interpret the base functor in the selective functor 'Over'.
toOver :: RW a -> Over [RW ()] b
toOver (R k _   ) = Over [void $ R k (const ())]
toOver (W k fv _) = void (runSelect toOver fv) *> Over [W k fv (const ())]

-- | Get all possible program effects.
getProgramEffects :: Program a -> [RW ()]
getProgramEffects = getOver . runSelect toOver

-- | A convenient alias for reading an element of the processor state.
read :: Key -> Program Value
read k = liftSelect (R k id)

-- | A convenient alias for writing into an element of the processor state.
write :: Key -> Program Value -> Program Value
write k fv = liftSelect (W k fv id)

-- --------------------------------------------------------------------------------
-- -------- Instructions ----------------------------------------------------------
-- --------------------------------------------------------------------------------

------------
-- Add -----
------------

-- | Read the values @x@ and @y@ and write the sum into @z@. If the sum is zero,
-- set the 'Zero' flag, otherwise reset it.
--
-- This implementation looks intuitive, but is incorrect, since the two write
-- operations are independent and the effects required for computing the sum,
-- i.e. @read x <*> read y@ will be executed twice. Consequently:
--   * the value written into @z@ is not guaranteed to be the same as the one
--     which was compared to zero,
--   * the static analysis of the computations would report more dependencies
--     than one might expect.
addNaive :: Key -> Key -> Key -> Program Value
addNaive x y z =
    let sum    = (+)   <$> read x <*> read y
        isZero = (==0) <$> sum
    in write (Flag Zero) (ifS isZero (pure 1) (pure 0)) *> write z sum

-- | This implementation of addition executes the effects associated with 'sum'
-- only once and then reuses it without triggering the effects again.
add :: Key -> Key -> Key -> Program Value
add x y z =
    let sum    = (+)   <$> read x <*> read y
        isZero = (==0) <$> write z sum
    in write (Flag Zero) (fromBool <$> isZero)

-----------------
-- jumpZero -----
-----------------
jumpZero :: Value -> Program ()
jumpZero offset =
    let pc       = read PC
        zeroSet  = (==1) <$> read (Flag Zero)
        modifyPC = void $ write PC ((+offset) <$> pc)
    in whenS zeroSet modifyPC

-- A block of instructions.
addAndJump :: Program ()
addAndJump = add (Reg R1) (Reg R2) (Reg R3) *> jumpZero 42

-----------------------------------
-- Add with overflow tracking -----
-----------------------------------

{-  The following example demonstrates how important it is to be aware of your
    effects.

    Problem: implement the semantics of the @add@ instruction which calculates
    the sum of two values and writes it to the specified destination, updates
    the 'Zero' flag if the result is zero, and also detects if integer overflow
    has occurred, updating the 'Overflow' flag accordingly.

    We'll take a look at two approaches that implement this semantics and see
    the crucial deference between them.
-}

-- | Add two values and detect integer overflow.
--
-- The interesting bit here is the call to the 'willOverflowPure' function.
-- Since the function is pure, the call @willOverflowPure <$> arg1 <*> arg2@
-- triggers only one 'read' of @arg1@ and @arg2@, even though we use the
-- variables many times in the 'willOverflowPure' implementation. Thus,
-- 'willOverflowPure' might be thought as an atomic processor microcommand.
addOverflow :: Key -> Key -> Key -> Program Value
addOverflow x y z =
    let arg1     = read x
        arg2     = read y
        result   = (+)   <$> arg1   <*> arg2
        isZero   = (==0) <$> write z result
        overflow = willOverflowPure <$> arg1 <*> arg2
    in write (Flag Zero)     (fromBool <$> isZero) *>
       write (Flag Overflow) (fromBool <$> overflow)

-- | A pure check for integer overflow during addition.
willOverflowPure :: Value -> Value -> Bool
willOverflowPure x y =
    let o1 = (>) y 0
        o2 = (>) x((-) maxBound y)
        o3 = (<) y 0
        o4 = (<) x((-) minBound y)
    in  (||) ((&&) o1 o2)
             ((&&) o3 o4)

-- | Add two values and detect integer overflow.
--
-- In this implementations we take a different approach and, when implementing
-- overflow detection, lift all the pure operations into 'Applicative'. This
-- forces the semantics to read the input variables more times than
-- 'addOverflow' does (@x@ is read 3x times, and @y@ is read 5x times).
--
-- It is not clear at the moment what to do with this. Should we just avoid this
-- style? Or could it sometimes be useful?
addOverflowNaive :: Key -> Key -> Key -> Program Value
addOverflowNaive x y z =
    let arg1   = read x
        arg2   = read y
        result = (+)   <$> arg1 <*> arg2
        isZero = (==0) <$> write z result
        overflow = willOverflow arg1 arg2
    in write (Flag Zero)     (fromBool <$> isZero) *>
       write (Flag Overflow) (fromBool <$> overflow)

-- | An 'Applicative' check for integer overflow during addition.
willOverflow :: Program Value -> Program Value -> Program Bool
willOverflow arg1 arg2 =
    let o1 = (>) <$> arg2 <*> pure 0
        o2 = (>) <$> arg1 <*> ((-) <$> pure maxBound <*> arg2)
        o3 = (<) <$> arg2 <*> pure 0
        o4 = (<) <$> arg1 <*> ((-) <$> pure minBound <*> arg2)
    in  (||) <$> ((&&) <$> o1 <*> o2)
             <*> ((&&) <$> o3 <*> o4)

-----------------------------------
-- Example simulations ------------
-----------------------------------

renderState :: State -> String
renderState state =
  "Registers: " <> show (registers state) <> "\n" <>
  "Flags: " <> show (Map.toList $ flags state) <> "\n" <>
  "Log: " <>  show (log state)

instance Show State where
    show = renderState

emptyRegisters :: RegisterBank
emptyRegisters = Map.fromList [(R0, 0), (R1, 0), (R2, 0), (R3, 0)]

emptyFlags :: Flags
emptyFlags = Map.fromList $ zip [Zero, Overflow] [0, 0..]

initialiseMemory :: [(Address, Value)] -> Memory
initialiseMemory m =
    let blankMemory = Map.fromList $ zip [0..maxBound] [0, 0..]
    in foldr (\(addr, value) acc -> Map.adjust (const value) addr acc) blankMemory m

boot :: Memory -> State
boot mem = State { registers = emptyRegisters
                 , pc = 0
                 , flags = emptyFlags
                 , memory = mem
                 , log   = []
                 }

twoAdds :: Program Value
twoAdds = add r0 (Cell 0) r0
          *>
          add r0 (Cell 0) r0

addExample :: IO ()
addExample = do
    let initState = boot (initialiseMemory [(0, 2)])
    print . snd $ runProgramState twoAdds initState

---------------------------- Some boilerplate code -----------------------------

instance (Show k, Show v) => Show (LogEntry  k v) where
    show (ReadEntry k v)  = "Read (" ++ show k ++ ", " ++ show v ++ ")"
    show (WriteEntry k v) = "Write (" ++ show k ++ ", " ++ show v ++ ")"
