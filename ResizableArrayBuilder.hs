{-# LANGUAGE BangPatterns #-}
module ResizableArrayBuilder where

import Data.Vector.Primitive.Mutable(IOVector)
import qualified Data.Vector.Primitive.Mutable as V
import Data.IORef
import qualified Data.ByteString as BS
import Data.Bits
import Data.Word
import Data.Int

import Data.Primitive.ByteArray
import Data.Primitive.Types(Addr(Addr))
import Data.ByteString.Internal
import Data.ByteString.Unsafe

data ResizableArrayBuilder =
     ResizableArrayBuilder !(IORef (IOVector Word8)) -- capacity
                           !(IORef Int)              -- actual size

rabToByteString (ResizableArrayBuilder rcap rsiz) = do
  v <- readIORef rcap
  s <- readIORef rsiz
  if s == 0
    then return BS.empty
    else case v of V.MVector _off _len mba -> do
                     pba <- newPinnedByteArray s
                     copyMutableByteArray pba 0 mba 0 s
                     let !(Addr addr_) = mutableByteArrayContents pba
                     unsafePackAddressLen s addr_

rabReadWord8 rab@(ResizableArrayBuilder rcap _rsiz) offset = do
  rabCheckLimit rab offset
  v <- readIORef rcap
  V.read v (fromIntegral offset)

rabSize (ResizableArrayBuilder _rcap rsiz) = do
  readIORef rsiz

newResizableArrayBuilder = do
  !v <- V.replicate 1 0xdd
  rcap <- newIORef v
  rsiz <- newIORef 0
  return $ ResizableArrayBuilder rcap rsiz

rabGrowToLimit :: ResizableArrayBuilder -> Word64 -> IO ()
rabGrowToLimit (ResizableArrayBuilder rcap rsiz) lim = do
  v0 <- readIORef rcap
  let !v0len = V.length v0
  let !newlen = fromIntegral $ grow (fromIntegral v0len) where grow v = if v <= lim then grow (2 * v) else v
  v' <- V.replicate newlen 0x00
  let !s = V.slice 0 v0len v'
  V.copy s v0
  writeIORef rcap v'

rabWriteBytes rab offset bs = do
  rabCheckLimit rab (offset + fromIntegral (BS.length bs))
  mapM_ (\n -> rabWriteWord8_ rab (offset + fromIntegral n) (BS.index bs n)) [0..BS.length bs]

rabCheckLimit :: ResizableArrayBuilder -> Word64 -> IO ()
rabCheckLimit rab@(ResizableArrayBuilder rcap rsiz) !lim = do
  modifyIORef' rsiz (\s -> let !v = max s (fromIntegral (lim + 1)) in v)
  !v <- readIORef rcap
  if fromIntegral (V.length v) <= lim
    then do rabGrowToLimit rab lim
    else return ()

rabWriteWord8_ !rab@(ResizableArrayBuilder rcap rsiz) !offset !value = do
  v <- readIORef rcap
  let !o = fromIntegral offset
  V.write v o value

rabWriteBit !rab !offset !bitoff !value = do
  let !(q,r) = divMod bitoff 8
  w <- rabReadWord8 rab (offset + fromIntegral q)
  let !w' = if value then setBit w r else clearBit w r
  rabWriteWord8_ rab (offset + fromIntegral q) w'
 
rabWriteWord8 :: ResizableArrayBuilder -> Word64 -> Word8 -> IO ()
rabWriteWord8 !rab@(ResizableArrayBuilder rcap rsiz) !offset !value = do
  rabCheckLimit rab offset
  rabWriteWord8_ rab offset value

rabWriteWord16 :: ResizableArrayBuilder -> Word64 -> Word16 -> IO ()
rabWriteWord16 !rab@(ResizableArrayBuilder rcap rsiz) !offset !value = do
  rabCheckLimit rab (offset + 1)
  rabWriteWord8_ rab (offset + 1) (fromIntegral (value `shiftR` 8) :: Word8)
  rabWriteWord8_ rab (offset + 0) (fromIntegral (value           ) :: Word8)

rabWriteWord32 :: ResizableArrayBuilder -> Word64 -> Word32 -> IO ()
rabWriteWord32 !rab@(ResizableArrayBuilder rcap rsiz) !offset !value = do
  rabCheckLimit rab (offset + 3)
  rabWriteWord8_ rab (offset + 3) (fromIntegral (value `shiftR` 24) :: Word8)
  rabWriteWord8_ rab (offset + 2) (fromIntegral (value `shiftR` 16) :: Word8)
  rabWriteWord8_ rab (offset + 1) (fromIntegral (value `shiftR`  8) :: Word8)
  rabWriteWord8_ rab (offset + 0) (fromIntegral (value            ) :: Word8)

rabWriteWord64 :: ResizableArrayBuilder -> Word64 -> Word64 -> IO ()
rabWriteWord64 !rab@(ResizableArrayBuilder rcap rsiz) !offset !value = do
  rabWriteWord32 rab (offset + 4) (fromIntegral (value `shiftR`  32) :: Word32)
  rabWriteWord32 rab (offset + 0) (fromIntegral (value             ) :: Word32)


rabWriteInt64 :: ResizableArrayBuilder -> Word64 -> Int64 -> IO ()
rabWriteInt64 !rab !offset !value = rabWriteWord64 rab offset (fromIntegral value)

rabWriteInt32 :: ResizableArrayBuilder -> Word64 -> Int32 -> IO ()
rabWriteInt32 !rab !offset !value = rabWriteWord64 rab offset (fromIntegral value)

rabWriteInt16 :: ResizableArrayBuilder -> Word64 -> Int16 -> IO ()
rabWriteInt16 !rab !offset !value = rabWriteWord64 rab offset (fromIntegral value)

rabWriteInt8 :: ResizableArrayBuilder -> Word64 -> Int8 -> IO ()
rabWriteInt8 !rab !offset !value = rabWriteWord64 rab offset (fromIntegral value)
