module Minuproto where

import Data.Int
import Data.Bits
import Data.Word
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.ByteString(ByteString)
import Data.Char(chr, toUpper)
import Data.List((!!), foldl')

import qualified Data.ByteString.Internal as BS(c2w)
import qualified Data.ByteString.Lazy.Builder as BD
import qualified Data.ByteString.Lazy as LBS
import Data.Monoid(mappend)

import ResizableArrayBuilder

import Text.PrettyPrint.ANSI.Leijen

import Debug.Trace(trace)

import Control.Monad.State

wordLE n a b = let cast = fromInteger . toInteger in
               shift (cast a) n .|. cast b

_w16 :: Word8 -> Word8 -> Word16
_w16 a b = wordLE 8 a b

_w32 :: Word16 -> Word16 -> Word32
_w32 a b = wordLE 16 a b

_w64 :: Word32 -> Word32 -> Word64
_w64 a b = wordLE 32 a b

bs8 :: ByteString -> (Word8, ByteString)
bs8 bs = case BS.uncons bs of
          Just res -> res
          Nothing -> (0, bs)

bs16 :: ByteString -> (Word16, ByteString)
bs16 bs0 = let (w0, bs1) = bs8 bs0 in
           let (w1, bs2) = bs8 bs1 in
           (_w16 w1 w0, bs2)

bs32 :: ByteString -> (Word32, ByteString)
bs32 bs0 = let (w0, bs1) = bs16 bs0 in
           let (w1, bs2) = bs16 bs1 in
           (_w32 w1 w0, bs2)

bs64 :: ByteString -> (Word64, ByteString)
bs64 bs0 = let (w0, bs1) = bs32 bs0 in
           let (w1, bs2) = bs32 bs1 in
           (_w64 w1 w0, bs2)

bsvoid bs = ((), bs)

at :: (ByteString -> (word, ByteString)) -> Int64 -> ByteString -> word
at _ n bs | BS.length bs <= fromIntegral n = error $ "ByteString too small for read at " ++ show n
at f n bs = let (v, _) = f (BS.drop (fromIntegral n) bs) in v

bs1b :: Int64 -> ByteString -> Bool
bs1b offset bs =
  let (byteoffset, bitoffset) = offset `divMod` 8 in
  let (v, _) = bs8 (BS.drop (fromIntegral byteoffset) bs) in
  testBit v (fromIntegral bitoffset)

isOdd n = (n `mod` 2) == 0

newtype WordOffset = WordOffset Int64 deriving (Show, Eq, Ord)
newtype ByteOffset = ByteOffset Int64 deriving (Show, Eq, Ord)

unWordOffset (WordOffset i) = i

liftWordOffset1 op (WordOffset a) = WordOffset (op a)
liftWordOffset2 op (WordOffset a) (WordOffset b) = WordOffset (op a b)

instance Num WordOffset where
  (+)    = liftWordOffset2 (+)
  (-)    = liftWordOffset2 (-)
  (*)    = liftWordOffset2 (*)
  negate = liftWordOffset1 negate
  abs    = liftWordOffset1 abs
  signum = liftWordOffset1 signum
  fromInteger i = WordOffset $ fromInteger i

word :: ByteString -> WordOffset -> Word64
word bs (WordOffset nw) =                at bs64 (8 * nw) bs

byte bs (ByteOffset nb) = fromIntegral $ at bs8  nb bs

slice off len bs = BS.take (fromIntegral len) (BS.drop (fromIntegral off) bs)
sliceWords off len bs = slice (8 * off) (8 * len) bs

mask n = ((shift 1 n) - 1)

splitU :: Int -> Word64 -> (Word64, Word64)
splitU n w = (w .&. mask n, shiftR w n)

splitS :: Int -> Word64 -> (Int64, Word64)
splitS n w = let (u, r) = splitU n w in
             if testBit u (n - 1)
               then (- (fromIntegral $ clearBit u (n - 1)), r)
               else (   fromIntegral   u, r)

splitSegments rawbytes =
  let numsegs = (at bs32 0 rawbytes) + 1 in
  let segsizes = [at bs32 (4 * (fromIntegral n)) rawbytes | n <- [1..numsegs]] in
  -- If we have an odd number of segments, the the segment lengths plus the #segs word
  -- will end word-aligned; otherwise, we need an extra padding word.
  let startsegpos = 4 * (fromIntegral numsegs + (if isOdd numsegs then 0 else 1)) in
  let allsegbytes = BS.drop startsegpos rawbytes in
  let segoffsets = scanl (+) 0 segsizes in
  let segs = [sliceWords offset len allsegbytes | (offset, len) <- zip segoffsets segsizes] in
  trace (show segsizes ++ " ;; " ++ show (BS.length rawbytes) ++ " vs " ++ show (zip segoffsets segsizes) ++ " ;; " ++ show (map BS.length segs)) $
    segs


data Pointer = StructPtr ByteString String WordOffset Word64      Word64 -- PointsInto, Origin, Offset, # data words, # ptr words
             | ListPtr   ByteString WordOffset WordOffset ListEltSize Word64 -- PointsInto, Origin, Offset, eltsize, # elts

instance Show Pointer where
  show (StructPtr _ _ off ndw npw) = "(StructPtr " ++ show ndw ++ " " ++ show npw ++ ")"
  show (ListPtr   _ orig off eltsz nelts) = "(ListPtr " ++ show orig ++ " " ++ show off ++ " " ++ show nelts ++ ")"

data FlatObj = StructFlat ByteString [Pointer]
             | ListFlat   [FlatObj]
             | StrFlat    String
             deriving Show

data Object = StructObj ByteString [Object]
            | ListObj   [Object]
            | StrObj     String
            | InvalidObj String
             deriving Show

dropLastByte str = take (length str - 1) str
unStrObj (StrObj str) = dropLastByte str
unStrObj (StructObj bs []) | BS.null bs = ""
unStrObj other = error $ "unStrObj wasn't expecting " ++ show other

mk_void :: Object -> ()
mk_void _ = ()

instance Pretty Object where
  pretty (StructObj bs    []     ) | BS.null bs = text "{{}}"
  pretty (ListObj         []     ) = text "{[]}"
  pretty (StructObj bs    objects) = parens $ text "StructObj" <$> indent 4 (text $ show bs)
                                                               <$> indent 4 (pretty objects)
  pretty (ListObj         objects) = parens $ text "ListObj"   <+> indent 4 (pretty objects)
  pretty (InvalidObj          str) = parens $ text "InvalidObj:" <+> text str
  pretty (StrObj              str) = text (show str)

parseUnknownPointerAt :: String -> ByteString -> [ByteString] -> WordOffset -> Pointer
parseUnknownPointerAt msg bs segs o =
 --trace ("parseUnknownPointerAt " ++ show o ++ " " ++ msg) $
  let w = bs `word` o in
  let (ptrtag, _) = splitU 2 w in
  case ptrtag of
    0 -> parseStructPointerAt bs o
    1 -> parseListPointerAt bs o
    2 -> parseInterSegmentPointerAt bs segs o
    _ -> error $ "parseUnknownPointer: " ++ show ptrtag ++ " At: " ++ show o

parseStructPointerAt :: ByteString -> WordOffset -> Pointer
parseStructPointerAt bs o =
  let w = bs `word` o in
  let (_a, w0) = splitU 2 w in
  let ( b, w1) = splitS 30 w0 in
  let ( c, w2) = splitU 16 w1 in
  let ( d, w3) = splitU 16 w2 in
  StructPtr bs (show o) (WordOffset b + o + 1) c d

w2i :: Word64 -> Int64
w2i = fromIntegral

derefStructPointer :: Pointer -> [ByteString] -> FlatObj
derefStructPointer (StructPtr bs origin off numdata numptrs) segs =
  StructFlat (sliceWords (unWordOffset off) numdata bs)
             [parseUnknownPointerAt ("fromstruct@" ++ origin) bs segs (off + WordOffset (w2i n))
               | n <- numdata `upby` numptrs]

readStructPointerAt o bs segs = derefStructPointer (parseStructPointerAt bs o) segs

parseListTagPointerAt :: ByteString -> WordOffset -> (Word64, Word64, Word64)
parseListTagPointerAt bs o =
  let w = bs `word` o in
  let (_a, w0) = splitU 2 w in
  let ( b, w1) = splitU 30 w0 in -- number of elements in the list
  let ( c, w2) = splitU 16 w1 in -- # data words, per elt.
  let ( d, w3) = splitU 16 w2 in -- # ptr  words, per elt.
  (b, c, d)

data ListEltSize = LES_Phantom
                 | LES_Bit
                 | LES_Byte1
                 | LES_Byte2
                 | LES_Byte4
                 | LES_Word
                 | LES_Ptr
                 | LES_Composite Word64 Word64 -- data/ptr words
                 deriving (Eq, Ord, Show)

lesFor 0 _ = LES_Phantom
lesFor 1 _ = LES_Bit
lesFor 2 _ = LES_Byte1
lesFor 3 _ = LES_Byte2
lesFor 4 _ = LES_Byte4
lesFor 5 _ = LES_Word
lesFor 6 _ = LES_Ptr
lesFor 7 (_, dw, pw) = LES_Composite dw pw
lesFor _ _ = error "unkonnw list size tag"

parseListPointerAt :: ByteString -> WordOffset -> Pointer
parseListPointerAt bs o =
  let w = bs `word` o in
  let (_a, w0) = splitU 2 w in
  let ( b, w1) = splitS 30 w0 in
  let ( c, w2) = splitU 3  w1 in
  let ( d, w3) = splitU 29 w2 in
  let list_target_offset = WordOffset b + o + 1 in
  let tagptr = parseListTagPointerAt bs list_target_offset in
  let numelts = if c == 7 then let (ne, _, _) = tagptr in ne else d in
  -- b is the "Offset, in words, from the end of the pointer to the
  -- start of the first element in the list. Signed."
  --trace ("list ptr @ " ++ show o ++ " had b=" ++ show b) $
   ListPtr bs o (list_target_offset + (if c == 7 then 1 else 0)) (lesFor c tagptr) numelts

zeroto n =
  if n > 0 then [0 .. fromIntegral (n - 1)]
           else []

upby k n = map (+k) (zeroto n)

byteOffsetOf (WordOffset o) = o * 8

charOfBool b = if b then '1' else '0'

readNthBit bs boff n =
  let (byteoff, bitoff) = (fromIntegral n) `divMod` 8 in
  readBitOfByte bitoff (boff + fromIntegral byteoff) bs

readBitOfByte :: Int64 -> Int64 -> ByteString -> Bool
readBitOfByte bit byt bs =
  let mask = (shiftL 1 (fromIntegral bit)) :: Int64 in
  ((byte bs (ByteOffset byt)) .&. mask) == mask

derefListPointer :: Pointer -> [ByteString] -> FlatObj
derefListPointer ptr@(ListPtr bs origin off eltsize numelts) segs =
  let boff = byteOffsetOf off in
  case eltsize of
    LES_Phantom -> ListFlat (replicate (fromIntegral numelts) (StructFlat BS.empty []))
    LES_Byte1   -> StrFlat [chr $ fromIntegral $ byte bs (ByteOffset $ boff + n) | n <- zeroto numelts]
    LES_Byte2   -> ListFlat [StructFlat (slice (8 * unWordOffset off + n) 2 bs)        [] | n <- zeroto numelts]
    LES_Word    -> ListFlat [StructFlat (sliceWords (unWordOffset off + n) 1 bs)        [] | n <- zeroto numelts]
    --LES_Bit     -> StrFlat [charOfBool (readNthBit bs boff n) | n <- zeroto numelts]
    LES_Bit     -> StrFlat $ "...bitlist(" ++ show numelts ++ ")..."
    LES_Composite dw pw ->
      let offsets = [off + (fromIntegral $ i * (dw + pw)) | i <- zeroto numelts] in
      ListFlat [derefStructPointer (StructPtr bs (show ptr ++ ";" ++ show off') off' dw pw) segs | off' <- offsets]
    _ -> error $ "can't yet parse list of elts sized " ++ show eltsize

parseInterSegmentPointerAt :: ByteString -> [ByteString] -> WordOffset -> Pointer
parseInterSegmentPointerAt bs segs o =
  let w = bs `word` o in
  let (_a, w0) = splitU 2 w in
  let ( b, w1) = splitU 1 w0 in
  let ( c, w2) = splitU 29 w1 in
  let ( d, w3) = splitU 32 w2 in
  if b == 0
    then let bs' = segs !! fromIntegral d in
         let pp = parseUnknownPointerAt "<<parseInterSegmentPointerAt>>" bs' segs (WordOffset (fromIntegral c)) in
          trace ("parseInterSegmentPointerAt " ++ show o ++ "; " ++ show d ++ " " ++ show pp) $ pp
    else error $ "parseInterSegmentPointerAt can't yet support doubly-indirect pointers."

unflatten :: Int -> [ByteString] -> FlatObj -> Object
unflatten 0 _ flat = InvalidObj $ "no gas left for " ++ show flat
unflatten n segs (StructFlat words ptrs) = StructObj words (map (derefUnknownPointer (n - 1) segs) ptrs)
unflatten n segs (ListFlat   flats) =        ListObj       (map (unflatten (n - 1) segs) flats)
unflatten _ _    (StrFlat    str)   =         StrObj str

derefUnknownPointer :: Int -> [ByteString] -> Pointer -> Object
derefUnknownPointer n segs ptr =
  unflatten n segs $
    case ptr of
      StructPtr {} -> derefStructPointer ptr segs
      ListPtr   {} -> derefListPointer   ptr segs

parseSegment :: ByteString -> [ByteString] -> Object
parseSegment bs segs =
  unflatten 99999 segs $ readStructPointerAt 0 bs segs

parseBytes rawbytes =
  let segments@(seg:_) = splitSegments rawbytes in
  let obj = parseSegment seg segments in
  obj

instance Pretty Word64 where pretty w = text (show w)

updateNextOffset :: ResizableArrayBuilder -> Word64 -> IO Word64
updateNextOffset rab prevoffset = do
  nextoffset <- rabSize rab
  return $ max prevoffset (fromIntegral nextoffset)

mapL :: String -> (Object -> t) -> Object -> [t]
mapL _ f (ListObj vals) = map f vals
mapL _ _ (StructObj bs []) | BS.null bs = []
mapL _ _ (StrObj "") = []
mapL msg f other = error $ "mapL("++msg++") can't map over " ++ show (pretty other) ++ " which is " ++ show other

objsLength objs = fromIntegral $ length objs

delta_in_words bo1 bo2 = (bo1 - bo2) `div` 8

sr_list_of_Type_Void voids rab ptr_off data_off = do
  sr_ptr_list rab ptr_off 0 (fromIntegral $ length voids) (delta_in_words data_off (ptr_off + 8))

sr_Type_UInt8  rab val data_off = rabWriteWord8  rab data_off val
sr_Type_UInt16 rab val data_off = rabWriteWord16 rab data_off val
sr_Type_UInt32 rab val data_off = rabWriteWord32 rab data_off val
sr_Type_UInt64 rab val data_off = rabWriteWord64 rab data_off val
sr_Type_Int8   rab val data_off = rabWriteInt8   rab data_off val
sr_Type_Int16  rab val data_off = rabWriteInt16  rab data_off val
sr_Type_Int32  rab val data_off = rabWriteInt32  rab data_off val
sr_Type_Int64  rab val data_off = rabWriteInt64  rab data_off val

sr_Type_Void :: ResizableArrayBuilder -> () -> Word64 -> IO ()
sr_Type_Void rab _unit _data_off = return ()

-- TODO...
sr_Type_Bool :: ResizableArrayBuilder -> Bool -> Word64 -> Int -> IO ()
sr_Type_Bool rab b data_off bit_off = do
  rabWriteBit rab data_off bit_off b

padbyte_offsets o n = [o.. o + n]

sr_Type_Text :: String -> ResizableArrayBuilder -> Word64 -> Word64 -> IO ()
sr_Type_Text str rab ptr_off data_off = do
    o <- foldM (\o c -> do rabWriteWord8 rab o (BS.c2w c)
                           return (o + 1)) data_off str
    let num_elts = length str + 1
    let num_pad_bytes = let excess = num_elts `mod` 8 in
                         if excess > 0 then 8 - excess else 0
    putStrLn $ "serializing text of length " ++ show num_elts ++ " (incl. null terminator), with # padding bytes = " ++ show num_pad_bytes ++ " ::: " ++ show (padbyte_offsets o (fromIntegral num_pad_bytes))
    putStrLn $ "text ptr is at " ++ show ptr_off ++ " and text data is at " ++ show data_off
    bp <- rabSize rab
    putStrLn $ "before padding, nextoffset will be " ++ show bp
    -- always writes at least one byte for nul terminator.
    mapM_ (\o -> do rabWriteWord8 rab o 0x00) (padbyte_offsets o (fromIntegral num_pad_bytes))
    bp <- rabSize rab
    putStrLn $ "after padding, nextoffset will be " ++ show bp
    sr_ptr_list rab ptr_off 2 (fromIntegral num_elts) (delta_in_words data_off (ptr_off + 8))

sr_ptr_list :: ResizableArrayBuilder -> Word64 -> Int -> Word64 -> Word64 -> IO ()
sr_ptr_list rab ptr_off size_tag num_elts delta = do
  let a_tag = 1
  putStrLn $ "emitting list ptr @ " ++ show ptr_off ++ " with tag/nelts/delta = " ++ show (size_tag, num_elts, delta) ++ " ; " ++ show ((fromIntegral size_tag + fromIntegral num_elts `shiftL` 3) :: Word32)
  rabWriteWord32 rab  ptr_off      (a_tag + fromIntegral delta `shiftL` 2)
  rabWriteWord32 rab (ptr_off + 4) (fromIntegral size_tag + fromIntegral num_elts `shiftL` 3)

sr_ptr_struct :: ResizableArrayBuilder -> Word64 -> Word16 -> Word16 -> Word64 -> IO ()
sr_ptr_struct rab ptr_off sizedata sizeptrs delta = do
  rabWriteWord32 rab  ptr_off     (fromIntegral delta `shiftL` 2)
  rabWriteWord16 rab (ptr_off + 4) sizedata
  rabWriteWord16 rab (ptr_off + 6) sizeptrs

sr_composite_list_helper :: ResizableArrayBuilder -> Word64 -> Word64 -> Word64 -> [s]
                         -> (s -> ResizableArrayBuilder -> Word64 -> Word64 -> IO ())
                         -> IO ()
sr_composite_list_helper rab objsize_bytes base_target_off base_ser_off objs helper = do
  let ser nextoffset (n, obj) = do
        let target_off = base_target_off + (objsize_bytes * n)
        helper obj rab target_off nextoffset
        nextoffset <- rabSize rab >>= return . fromIntegral
        return nextoffset
  foldM_ ser base_ser_off (zip [0..] objs)

sr_total_size_for 1 _ num_elts = error $ "size of multiple bits"
sr_total_size_for 7 struct_size num_elts = struct_size * num_elts
sr_total_size_for sizecode _    num_elts =
  num_elts * case sizecode of
               2 -> 1
               3 -> 2
               4 -> 4
               5 -> 8
               6 -> 8
               _ -> error $ "sr_total_size got wrong sizecode"

serializeWith :: a -> (a -> ResizableArrayBuilder -> Word64 -> Word64 -> IO ()) -> IO ByteString
serializeWith obj serializer = do
  rab <- newResizableArrayBuilder
  serializer obj rab 0 8 -- ptr offset, data offset
  bs <- rabToByteString rab
  return $ frameCapnProtoMessage bs

frameCapnProtoMessage :: ByteString -> ByteString
frameCapnProtoMessage bs =
  let frame = BD.byteString bs in
    LBS.toStrict $ BD.toLazyByteString $
      BD.word32LE 0 `mappend` BD.word32LE (fromIntegral (BS.length bs `div` 8)) `mappend` frame


