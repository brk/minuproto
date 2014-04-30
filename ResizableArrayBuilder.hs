module ResizableArrayBuilder where

import Data.Vector.Primitive.Mutable(IOVector)
import qualified Data.Vector.Primitive.Mutable as V
import Data.IORef
import qualified Data.ByteString as BS
import Data.Bits
import Data.Word
import Data.Int

data ResizableArrayBuilder =
     ResizableArrayBuilder (IORef (IOVector Word8)) -- capacity
                           (IORef Int)              -- actual size

rabToByteString (ResizableArrayBuilder rcap rsiz) = do
  v <- readIORef rcap
  s <- readIORef rsiz
  if s == 0
    then return BS.empty
    else do words <- sequence [V.read v i | i <- [0 .. s - 1]]
            return $ BS.pack words

rabSize (ResizableArrayBuilder _rcap rsiz) = do
  readIORef rsiz

newResizableArrayBuilder = do
  v <- V.replicate 1 0xdd
  rcap <- newIORef v
  rsiz <- newIORef 0
  return $ ResizableArrayBuilder rcap rsiz

rabGrow (ResizableArrayBuilder rcap rsiz) = do
  v0 <- readIORef rcap
  v' <- V.replicate (2 * V.length v0) 0x00
  V.copy (V.slice 0 (V.length v0) v') v0
  writeIORef rcap v'

rabCheckLimit :: ResizableArrayBuilder -> Word64 -> IO ()
rabCheckLimit rab@(ResizableArrayBuilder rcap rsiz) lim = do
  modifyIORef rsiz (\s -> max s (fromIntegral (lim + 1)))
  v <- readIORef rcap
  if fromIntegral (V.length v) <= lim
    then do rabGrow rab ; rabCheckLimit rab lim
    else return ()

rabWriteWord8_ rab@(ResizableArrayBuilder rcap rsiz) offset value = do
  v <- readIORef rcap
  V.write v (fromIntegral offset) value
 
rabWriteWord8 :: ResizableArrayBuilder -> Word64 -> Word8 -> IO ()
rabWriteWord8 rab@(ResizableArrayBuilder rcap rsiz) offset value = do
  rabCheckLimit rab offset
  rabWriteWord8_ rab offset value

rabWriteWord16 :: ResizableArrayBuilder -> Word64 -> Word16 -> IO ()
rabWriteWord16 rab@(ResizableArrayBuilder rcap rsiz) offset value = do
  rabCheckLimit rab (offset + 1)
  rabWriteWord8_ rab (offset + 1) (fromIntegral (value `shiftR` 8) :: Word8)
  rabWriteWord8_ rab (offset + 0) (fromIntegral (value           ) :: Word8)

rabWriteWord32 :: ResizableArrayBuilder -> Word64 -> Word32 -> IO ()
rabWriteWord32 rab@(ResizableArrayBuilder rcap rsiz) offset value = do
  rabCheckLimit rab (offset + 3)
  rabWriteWord8_ rab (offset + 3) (fromIntegral (value `shiftR` 24) :: Word8)
  rabWriteWord8_ rab (offset + 2) (fromIntegral (value `shiftR` 16) :: Word8)
  rabWriteWord8_ rab (offset + 1) (fromIntegral (value `shiftR`  8) :: Word8)
  rabWriteWord8_ rab (offset + 0) (fromIntegral (value            ) :: Word8)

rabWriteWord64 :: ResizableArrayBuilder -> Word64 -> Word64 -> IO ()
rabWriteWord64 rab@(ResizableArrayBuilder rcap rsiz) offset value = do
  rabWriteWord32 rab (offset + 4) (fromIntegral (value `shiftR`  32) :: Word32)
  rabWriteWord32 rab (offset + 0) (fromIntegral (value             ) :: Word32)


rabWriteInt64 :: ResizableArrayBuilder -> Word64 -> Int64 -> IO ()
rabWriteInt64 rab offset value = rabWriteWord64 rab offset (fromIntegral value)

rabWriteInt32 :: ResizableArrayBuilder -> Word64 -> Int32 -> IO ()
rabWriteInt32 rab offset value = rabWriteWord64 rab offset (fromIntegral value)

rabWriteInt16 :: ResizableArrayBuilder -> Word64 -> Int16 -> IO ()
rabWriteInt16 rab offset value = rabWriteWord64 rab offset (fromIntegral value)

rabWriteInt8 :: ResizableArrayBuilder -> Word64 -> Int8 -> IO ()
rabWriteInt8 rab offset value = rabWriteWord64 rab offset (fromIntegral value)
