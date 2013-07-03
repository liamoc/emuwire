{-# LANGUAGE TupleSections, RankNTypes, Arrows, MultiWayIf, TemplateHaskell, FlexibleContexts, ImplicitParams, GeneralizedNewtypeDeriving #-}

import Data.Vector.Unboxed hiding (modify)
import Control.Lens
import Data.Word
import Data.Int
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative
import Data.Maybe


import qualified Data.Bits as B
import Data.Bits.Lens

data MachineState = MachineState
                  { _accumulator :: Word8
                  , _xIndex      :: Word8
                  , _yIndex      :: Word8
                  , _pc          :: Word16
                  , _sp          :: Word8
                  , _status      :: Word8
                  , _memoryVec   :: Vector Word8
                  }
makeLenses ''MachineState

type ZeroPageAddress = Word8
type Address = Word16
type StatusBit = Word8

type Cycles = Sum Int

narrow :: Word16 -> Word8
narrow = fromIntegral

broaden :: Word8 -> Word16
broaden = fromIntegral

hi :: Lens' Word16 Word8
hi f w = fmap (\v -> flip B.shiftL 8 (broaden v) B..|. (w B..&. 0x00FF))
              (f $ narrow $ flip B.shiftR 8 $ w B..&. 0xFF00)

lo :: Lens' Word16 Word8
lo f w = fmap (\v -> broaden v B..|. (w B..&. 0xFF00) )
              (f $ narrow $ w B..&. 0x00FF)


delay :: (MonadWriter Cycles m) => Int -> a -> m a
delay x a = tell (Sum x) >> return a

wait ::  (MonadWriter Cycles m) => Int -> m ()
wait = tell . Sum

memory :: Address -> Lens' MachineState Word8
memory a = singular (memoryVec . ix (fromIntegral a))

-- assumption, two input lenses do not alias
also :: Lens' a b -> Lens' a c -> Lens' a (b,c)
also lab lac = lens (\s -> (s^.lab, s^.lac))
                    (\s (b,c) -> s & lab .~ b & lac .~ c)

memoryW :: Address -> Lens' MachineState Word16
memoryW a = (memory a `also` memory (a+1)) . combine

combine :: Iso' (Word8,Word8) Word16
combine = iso (flip (set $ lo `also` hi) 0)
               (view (lo `also` hi))


readOperand' :: (MonadWriter Cycles m) => MemOperand -> MachineState -> m Word8
readOperand' (Immediate v) s = delay 0 v
readOperand' (ZeroPage  a) s = delay 1 (s^.memory (broaden a))
readOperand' (Absolute  a) s = delay 2 (s^.memory a)
readOperand' (ZPIndexedX a) s = delay 2 (s^.memory ( broaden $ s^.xIndex + a))
readOperand' (ZPIndexedY a) s = delay 2 (s^.memory ( broaden $ s^.yIndex + a))
readOperand' (IndexedX  a) s = let v = (s^.xIndex.to broaden + a)
                                   c = v^.hi == a^.hi
                                in delay (2 + if c then 1 else 0) (s^.memory v)
readOperand' (IndexedY  a) s = let v = (s^.yIndex.to broaden + a)
                                   c = v^.hi == a^.hi
                                in delay (2 + if c then 1 else 0) (s^.memory v)
readOperand' (PreIndexedIndirect a) s = let v = broaden (s^.xIndex + a)
                                         in delay 4 $ s^.memory (s^.memoryW v)
readOperand' (PostIndexedIndirect a) s = let v  = s^.memoryW (broaden a)
                                             v' = v + s^.yIndex.to broaden
                                             c  = v^.hi == v'^.hi
                                          in delay (3 + if c then 1 else 0) $ s^.memory v'

writeOperand' :: (MonadWriter Cycles m) => MemOperand -> Word8 -> MachineState -> m (MachineState)
writeOperand' (Immediate  v) _ = error "Can't write to immediate"
writeOperand' (ZeroPage   a) v = delay 1 . (memory (broaden a) .~ v)
writeOperand' (Absolute   a) v = delay 2 . (memory a .~ v)
writeOperand' (IndexedX   a) v = delay 3 . \s -> s & memory (s^.xIndex.(to broaden) + a) .~ v
writeOperand' (IndexedY   a) v = delay 3 . \s -> s & memory (s^.yIndex.(to broaden) + a) .~ v
writeOperand' (ZPIndexedX a) v = delay 2 . \s -> s & memory (broaden $ s^.xIndex + a) .~ v
writeOperand' (ZPIndexedY a) v = delay 2 . \s -> s & memory (broaden $ s^.yIndex + a) .~ v
writeOperand' (PreIndexedIndirect a) v
    = delay 4 . \s -> let a' = s^.memoryW (broaden $ s^.xIndex + a)
                       in s & memory a' .~ v
writeOperand' (PostIndexedIndirect a) v
    = delay 4 . \s -> let a' = s^.memoryW (broaden a) + s^.yIndex.to broaden
                       in s & memory a' .~ v

newtype Emu a = Emu (WriterT (Sum Int) (State MachineState) a)
     deriving ( MonadWriter (Sum Int)
              , MonadState MachineState
              , Monad
              , Applicative
              , Functor
              )

readOperand :: MemOperand -> Emu Word8
readOperand o = get >>= readOperand' o

writeOperand :: MemOperand -> Word8 -> Emu ()
writeOperand o v = get >>= writeOperand' o v >>= put

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




bitAsWord8 :: Int -> Prism' Word8 Bool
bitAsWord8 i = prism' (\x -> if x then B.bit i else 0) (\x -> if | x == 0       -> Just False
                                                                 | x == B.bit i -> Just True
                                                                 | otherwise    -> Nothing )

adc :: MemOperand -> Emu ()
adc o = do a <- use accumulator
           b <- readOperand o
           c <- use (status.bitAt carry.re (bitAsWord8 carry))
           let (hi, lo) = (broaden a + broaden b + broaden c) ^. from combine
           accumulator .= lo
           status.bitAt carry .= (hi /= 0)
           status.bitAt zero .= (lo == 0)
           status.bitAt negative .= (lo B..&. 0x80 /= 0)
           status.bitAt signedOverflow .= (B.complement (a `B.xor` b)
                                                 B..&.(a `B.xor` lo)
                                                 B..&. 0x80 /= 0)

and :: MemOperand -> Emu ()
and o = do m <- readOperand o
           a' <- accumulator <.&.= m
           status.bitAt zero .= (a' == 0)
           status.bitAt negative .= (a' B..&. 0x80 /= 0)

aslA :: Emu ()
aslA = do accumulator %= flip B.rotateL 1
          c <- use $ accumulator.bitAt 0
          status.bitAt carry .= c
          accumulator.bitAt 0 .= False

asl :: MemOperand -> Emu ()
asl o = do x <- readOperand o
           let v = B.rotateL x 1
           status.bitAt carry .= v^.bitAt 0
           writeOperand o (v & bitAt 0 .~ False)

jmp :: Word16 -> Emu ()
jmp a = do pc .= a
           wait 1

jmpi :: Word16 -> Emu ()
jmpi a = do use (memoryW a) >>= jmp
            wait 2

branch :: Int8 -> Emu ()
branch w = do p  <- use pc
              p' <- pc <+= fromIntegral w
              wait $ if (p^.hi == p'^.hi) then 1 else 2


bcs :: Int8 -> Emu ()
bcs l = wait 2 >> use (status.bitAt carry) >>= flip when (branch l)

bcc :: Int8 -> Emu ()
bcc l = wait 2 >> use (status.bitAt carry.to not) >>= flip when (branch l)

beq :: Int8 -> Emu ()
beq l = wait 2 >> use (status.bitAt zero) >>= flip when (branch l)

bne :: Int8 -> Emu ()
bne l = wait 2 >> use (status.bitAt zero.to not) >>= flip when (branch l)

bmi :: Int8 -> Emu ()
bmi l = wait 2 >> use (status.bitAt negative) >>= flip when (branch l)

bpl :: Int8 -> Emu ()
bpl l = wait 2 >> use (status.bitAt negative.to not) >>= flip when (branch l)

bit :: MemOperand -> Emu ()
bit (ZeroPage v) = bit (Absolute (broaden v)) >> wait (-1)
bit (Absolute v) = do x <- use accumulator
                      x' <- use (memory v)
                      status.bitAt zero .= (x B..&. x' == 0)
                      status.bitAt signedOverflow .= (x' ^. bitAt 6)
                      status.bitAt negative .= (x' ^. bitAt 7)
                      wait 4
bit _            = error "bit not defined for anything but absolute addressing"

brk :: Emu ()
brk = undefined



carry, signedOverflow, zero, negative :: Int
carry = 0
signedOverflow = 6
interrupt = 4
disableInterrupt = 2
decimalMode = 3
zero = 1
negative = 7

main = return ()
