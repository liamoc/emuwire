{-# LANGUAGE TupleSections #-}
import Control.Wire
import Control.Wire.Trans.Simple
import Control.Wire.Wire
import Prelude hiding ((.), id)
import Control.Monad.Identity
import Text.Printf
import Data.Word
import Data.Bits
import Data.Vector.Unboxed.Mutable as V



type WireI a b = Wire () IO a b

data MemOperand = Immediate Word8
                | ZeroPage ZeroPageAddress
                | Absolute Address
                | IndexedX Address
                | IndexedY Address
                | ZPIndexedX ZeroPageAddress
                | ZPIndexedY ZeroPageAddress -- not sure if necessary
                | PreIndexedIndirect ZeroPageAddress
                | PostIndexedIndirect ZeroPageAddress

data Instruction = CLC
                 | NOP
                 | ADC MemOperand
                 | AND MemOperand

type Cycles = Int
type Register = WireI Word8 Word8
type RegisterW = WireI Word16 Word16
type Carry = Bool
type SignedOverflow = Bool
type Address = Word16
type ZeroPageAddress = Word8
type StatusBit = Word8

broaden :: Word8 -> Word16
broaden = fromIntegral

asWord :: Word8 -> Word8 -> Word16
asWord a b = broaden a .|. shiftL (broaden b) 8

stuff = do
  memVec <- unsafeNew 65536
  let ifW' :: a -> a -> WireI Bool a
      ifW' t e = arr (\x -> if x then t else e)

      cond :: (a -> Bool) -> WireI Bool b -> WireI a a
      cond a b = preserve $ b . arr a

      preserve :: WireI a b -> WireI a a
      preserve a = snd <$> (a &&& id)

      accumulator , xindex , yindex , status , sp :: Register
      accumulator = hold 0 id
      xindex = hold 0 id
      yindex = hold 0 id
      status = hold 0 id
      sp = hold 0 id

      carry, signedOverflow, zero, negative :: StatusBit
      carry = 0x01
      signedOverflow = 0x20
      zero = 0x02
      negative = 0x80

      pc :: RegisterW
      pc = hold 0 id

      -- this is not actually possible, have to fix fetch.
      opCode :: Word8 -> Instruction
      opCode = undefined

      -- general type to work with PC too. Can compose directly with the register but
      -- this means you risk writing to it in complex chains.
      readRegister :: WireI s s -> WireI a s
      readRegister r = r . empty

      -- withRegister r f partially applies f to the value in r, producing a wire
      -- that you can compose.
      withRegister :: Register -> (Word8 -> Word8 -> Word8) -> WireI Word8 Word8
      withRegister r f = liftA2 f (readRegister r) id

      -- modify the value in a register
      modRegister :: Register -> (Word8 -> Word8) -> WireI a Word8
      modRegister r f = r . (f <$> readRegister r)

      -- A wire that adds the value in a register to its input
      addRegister :: Register -> WireI Word8 Word8
      addRegister r = withRegister r (+)

      -- Returns the the register + input and whether such an add crossed a page boundary
      addRegisterW :: Register -> WireI Word16 (Word16, Bool)
      addRegisterW r = liftA2 addW (broaden <$> readRegister r) id
          where addW r a = (r + a, not ((r + a) .&. 0xFF00 == a .&. 0xFF00))

      -- Add a register (presumably the accumulator) with a word8 and a carry bit, giving the sum
      -- carry bit and signed overflow bit. Used for ADC instruction
      addRegisterWithCarry :: Register -> WireI (Word8 , Carry) (Word8 , (Carry, SignedOverflow))
      addRegisterWithCarry r = liftA2 adc (readRegister r) id
        where adc :: Word8 -> (Word8, Carry) -> (Word8, (Carry, SignedOverflow))
              adc w1 (w2 , c) = let c' = if c then 1 else 0
                                    acc = w1 + w2 + c'
                                    carry = shiftR (broaden w1 + broaden w2 + broaden c') 8 /= 0
                                    so = ((acc `xor` w1) .&. (w2 `xor` w1) .&. 0x80) /= 0
                                 in (acc, (carry , so))

      -- Read from memory at a: send (a, Nothing) to memory and the result is the byte at that loc.
      -- Write v to memory at a: send (a, Just v) to memory and the result is the value you just wrote.
      memory :: WireI (Address, Maybe Word8) Word8
      memory = mkFixM (\_ (loc , set) -> maybe (return ()) (write memVec $ fromIntegral loc) set
                                      >> fmap Right (V.read memVec $ fromIntegral loc))

      -- helper to make reading memory easier.
      readMemory :: WireI Address Word8
      readMemory = lmap (,Nothing) memory

      -- Read two contiguous bytes in memory.
      readWord :: WireI Address Word16
      readWord = uncurry asWord <$> (readMemory &&& (readMemory . arr (+1)))

      -- Interpret a memory access operand, returning the value and the number of cycles
      -- that took to read.
      readOperand :: WireI MemOperand (Word8, Cycles)
      readOperand = switch (arr readOp) empty
       where readOp (Immediate  x) = (,2) <$> constant x
             readOp (ZeroPage   x) = (,3) <$> readMemory . pure (broaden x)
             readOp (Absolute   x) = (,4) <$> readMemory . pure x
             readOp (IndexedX   x) = (readMemory *** ifW' 4 5) . addRegisterW xindex . pure x
             readOp (IndexedY   x) = (readMemory *** ifW' 4 5) . addRegisterW yindex . pure x
             readOp (ZPIndexedX x) = (,4) <$> readMemory . (broaden <$> addRegister xindex . pure x)
             readOp (ZPIndexedY x) = (,4) <$> readMemory . (broaden <$> addRegister yindex . pure x)
             readOp (PreIndexedIndirect  x) = (,6) <$> readMemory
                                            . readWord
                                            . (broaden <$> addRegister xindex . pure x)
             readOp (PostIndexedIndirect x) = (readMemory *** ifW' 5 6)
                                            . addRegisterW yindex
                                            . readWord
                                            . pure (broaden x)

      -- Get a status bit from the status register
      getBit :: StatusBit -> WireI a Bool
      getBit b = ((/= 0) <$> (b .&.) <$> readRegister status)

      -- Set/clear a status bit in the status register
      setBit :: StatusBit -> WireI Bool Word8
      setBit b = ifW id (modRegister status (.|. b)) (modRegister status (.&. complement b))

      -- The main processor
      chooseCircuit :: Instruction -> WireI Instruction Cycles
      chooseCircuit CLC = constant 2 . modRegister status (.&. 0xFE)
      chooseCircuit NOP = constant 2
      chooseCircuit (ADC op) = snd <$>
                               first ( ( cond (== 0) (setBit zero)     -- TODO? decimal mode?
                                       . cond ((/= 0) . (.&. 0x80)) (setBit negative)
                                       . accumulator
                                     *** setBit carry
                                     *** setBit signedOverflow)
                                     . addRegisterWithCarry accumulator
                                     . (id &&& getBit carry)
                                     )
                             . readOperand
                             . pure op
      chooseCircuit (AND op) = snd <$>
                               first (accumulator . withRegister accumulator (.&.))
                             . readOperand . pure op

      -- Todo, read multi byte instructions
      fetch :: WireI a Instruction
      fetch = opCode <$> memory . fmap (, Nothing) (readRegister pc)

   in do return () :: IO ()
         return $ switch (arr chooseCircuit) empty . fetch


main :: IO ()
main =  undefined -- loop secondClock clockSession
  where
     loop w' session' = do
         (mx, w, session) <- stepSessionP w' session' ()
         case mx of
           Left ex -> return () -- putStrLn ("Inhibited: " ++ show ex)
           Right x -> putStrLn ("Produced: " ++ show x)
         loop w session
