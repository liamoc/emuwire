{-# LANGUAGE TupleSections #-}
import Control.Wire
import Prelude hiding ((.), id)
import Control.Monad.Identity
import Text.Printf
import Data.Word
import Data.Bits
import Data.Vector.Unboxed.Mutable as V



type WireI a b = Wire () IO a b

data Instruction = CLC

stuff :: IO ()
stuff = do 
  memVec <- unsafeNew 65536 
  let accumulator , xindex , yindex , status , sp :: WireI Word8 Word8
      accumulator = hold 0 id
      xindex = hold 0 id
      yindex = hold 0 id
      status = hold 0 id
      sp = hold 0 id

      memory :: WireI (Word16, Maybe Word8) Word8
      memory = mkFixM (\_ (loc , set) -> maybe (return ()) (write memVec $ fromIntegral loc) set
                                      >> fmap Right (V.read memVec $ fromIntegral loc))

      index :: WireI Word8 Word16
      index = (\a b -> a .|. shiftL b 8) <$> (broaden <$> xindex) <*> (broaden <$> yindex)

      broaden :: Word8 -> Word16
      broaden = fromIntegral

      opCode :: Word8 -> Instruction
      opCode = undefined

      fetch :: WireI a Instruction
      fetch = opCode <$> memory . fmap (, Nothing) (pc . empty)

      pc :: WireI Word16 Word16
      pc = hold 0 id
  undefined


main :: IO ()
main =  undefined -- loop secondClock clockSession
  where
     loop w' session' = do
         (mx, w, session) <- stepSessionP w' session' ()
         case mx of
           Left ex -> return () -- putStrLn ("Inhibited: " ++ show ex)
           Right x -> putStrLn ("Produced: " ++ show x)
         loop w session
