module Main where

import ResizableArrayBuilder
import qualified Data.ByteString as BS

main = do
  r <- newResizableArrayBuilder
  b0 <- rabToByteString r
  print b0


  l0 <- rabSize r
  rabWriteWord8 r 0 0
  l1 <- rabSize r
  rabWriteWord32 r 0 0x04030201
  rabGrow r
  l2 <- rabSize r
  rabWriteWord8 r 8 67
  l3 <- rabSize r
  b <- rabToByteString r
  print b
  print $ BS.unpack b
  print $ show (l0, l1, l2, l3)
