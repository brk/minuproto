{-# LANGUAGE BangPatterns #-}
module Minuproto 
{- (
                  -- Generic helpers, used by both generated code
                  -- and by the Main.hs bootstrapping
                  at, bs1b, bs8, bs16, bs32, bs64, mapL, unStrObj, Object(..),

                  -- Helpers for bootstrapping, not used by generated code.
                  splitSegments, parseSegment, readNthBit,

                  -- Helpers for generated code, not used by bootstrapping
                  parseBytes, serializeWith, delta_in_words, updateNextOffset,
                  bsvoid, mk_void, sr_Type_Void,
                  sr_Type_UInt64, sr_Type_UInt32, sr_Type_UInt16, sr_Type_UInt8, sr_Type_Bool,
                  sr_Type_Int64,  sr_Type_Int32,  sr_Type_Int16,  sr_Type_Int8,
                  sr_Type_Text, objsLength, sr_total_size_for,
                  sr_ptr_list, sr_ptr_struct, sr_composite_list_helper,
                  sr_list_of_Type_Void
                  ) -} where
import Prelude hiding ((<$>))
import Data.Int
import Data.Bits
import Data.Word
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.ByteString(ByteString)
import Data.Char(chr, toUpper)
import Data.List((!!), foldl')

import Numeric
import Data.Binary.IEEE754(doubleToWord, wordToDouble)

import qualified Data.Text as T
import qualified Data.Text.Encoding as T

import qualified Data.ByteString.Internal as BS(c2w)
import qualified Data.ByteString.Lazy.Builder as BD
import qualified Data.ByteString.Lazy as LBS
import Data.Monoid(mappend)

import ResizableArrayBuilder

import Text.PrettyPrint.ANSI.Leijen

import Debug.Trace(trace)

import Control.Monad.State

---------------------------------------------------------------------
type Offset = Int
---------------------------------------------------------------------

data StrictMaybe a = StrictlyNone
                   | StrictlyJust !a

instance Show a => Show (StrictMaybe a) where
  show  StrictlyNone    =  "StrictlyNone"
  show (StrictlyJust v) = "(StrictlyJust " ++ show v ++ ")"

---------------------------------------------------------------------
type List t = [t]

data ListEltSizeAlt
  = LESA_Phantom
  | LESA_Bit
  | LESA_Byte1
  | LESA_Byte2
  | LESA_Byte4
  | LESA_Word
  | LESA_Ptr
  | LESA_Composite Int -- // data+ptr words


pr_Float64 bs segs idx = wordToDouble (bs64  idx bs)
pr_Word64 bs segs idx = bs64  idx bs
pr_Word32 bs segs idx = bs32  idx bs
pr_Word16 bs segs idx = bs16  idx bs
pr_Word8  bs segs idx = bs8   idx bs
pr_Int64  bs segs idx = bs64i idx bs
pr_Int32  bs segs idx = bs32i idx bs
pr_Int16  bs segs idx = bs16i idx bs
pr_Int8   bs segs idx = bs8i  idx bs


getTargetOffsetOfPtr_ bs segs o =
  let w = bs `wordS` o in
  let (tag, w0) = splitU 2 w in

  case tag of
       0 -> let (b, w1) = splitS 30 w0 in
            (,) bs (fromIntegral b + o + 1)
       1 -> 
            let (b, w1) = splitS 30 w0 in
            (,) bs (fromIntegral b + o + 1)
       2 ->
            let ( b, w1) = splitU 1 w0 in
            let ( c, w2) = splitU 29 w1 in
            let ( d, w3) = splitU 32 w2 in
            if b == 0
              then let bs_ = lookupSegment segs (fromIntegral d) ("getTargetOffsetOfPtr_ o=" ++ show o ++ "; w =" ++ showHex w "") in
                   getTargetOffsetOfPtr_ bs_ segs (fromIntegral c)
              else error $ "getTargetOffsetOfPtr_ can't yet support doubly-indirect pointers."
       _ -> error $ "saw unknown ptr instead of struct ptr"

prText bs segs loc =
  (dropLastByte $ parseBytesFrom bs segs loc, ())

prBytes bs segs loc = parseBytesFrom bs segs loc

--parseBytesFrom :: { ByteString => List ByteString => Int64 => ByteString };
parseBytesFrom :: ByteString -> List ByteString -> Int64 -> ByteString
parseBytesFrom bs segs o =
  let w = bs `wordS` o in
  let (tag, w0) = splitU 2 w in
  case tag of
       0 ->
            error $ "parseBytesFrom saw struct ptr instead of list ptr"
       1 ->
            let (b, w1) = splitS 30 w0 in
            let (c, w2) = splitU 3  w1 in
            let (d, w3) = splitU 29 w2 in
            let target_off = fromIntegral b + o + 1 in
            let numelts = fromIntegral d in

            slice (fromIntegral $ target_off * 8) numelts bs
       2 ->
            let (b, w1) = splitU 1 w0 in
            let (c, w2) = splitU 29 w1 in
            let (d, w3) = splitU 32 w2 in
            if b == 0
              then let bs_ = lookupSegment segs (fromIntegral d) ("parseBytesFrom o=" ++ show o ++ "; w =" ++ showHex w "") in
                   parseBytesFrom bs_ segs (fromIntegral c)
              else 
                   error $ "parseBytesFrom can't yet support doubly-indirect pointers."
       _ -> 
            error $ "saw unknown ptr instead of list ptr"

-- parsePointee :: forall t:Type, { ByteString => List ByteString => { ByteString => List ByteString => Int64 => t } => Int64 => t };
parsePointee bs segs pr loc =
  let (bs_, loc_) = getTargetOffsetOfPtr_ bs segs loc in
  pr bs_ segs loc_

-- parsePointeeMb :: forall t:Type, { ByteString => List ByteString => { ByteString => List ByteString => Int64 => t } => Int64 => StrictMaybe t };
parsePointeeMb bs segs pr loc =
  if (bs `wordS` loc) == 0
    then StrictlyNone
    else
      let (bs_, off_) = getTargetOffsetOfPtr_ bs segs loc in
      StrictlyJust (pr bs_ segs off_)

--parsePointerMb :: forall t:Type, { ByteString => List ByteString => { ByteString => List ByteString => Int64 => t } => Int64 => StrictMaybe t };
parsePointerMb  bs segs pr loc =
  if (bs `wordS` loc) == 0
    then StrictlyNone
    else StrictlyJust (pr bs segs loc)

--parseVoidListFrom :: { ByteString => List ByteString => Int64 => Array () };
parseVoidListFrom  bs segs o =
  let (bs_, target_off, tag, numelts) = parseListPointerAt_ bs segs o in
  [() | n <- zeroto numelts]

--parseBitListFrom :: { ByteString => List ByteString => Int64 => Array Bool };
parseBitListFrom bs_ segs o =
  let (bs, target_off, tag, numelts) = parseListPointerAt_ bs_ segs o in
  let boff = target_off * 8 in
  [readNthBitS bs boff n | n <- zeroto numelts]

parseListFromMb bs_ segs pr o_ =
  let (bs, target_off, tag, numelts) = parseListPointerAt_ bs_ segs o_ in
  if (bs `wordS` target_off) == 0
    then StrictlyNone
    else StrictlyJust (parseListFrom bs segs pr target_off)

parseListFrom bs_ segs pr o_ =
  let (bs, target_off, tag, numelts) = parseListPointerAt_ bs_ segs o_ in
  if (bs `wordS` target_off) == 0
    then []
    else
      let boff = target_off * 8 in
      case tag of
        LESA_Phantom -> error $ "parseListFrom invariant violated"
        LESA_Bit     -> error $ "parseListFrom invariant violated"
        LESA_Byte1   -> [pr bs segs (boff + (1 * (fromIntegral numelts))) | n <- zeroto numelts]
        LESA_Byte2   -> [pr bs segs (boff + (2 * (fromIntegral numelts))) | n <- zeroto numelts]
        LESA_Byte4   -> [pr bs segs (boff + (4 * (fromIntegral numelts))) | n <- zeroto numelts]
        LESA_Word    -> [pr bs segs (boff + (8 * (fromIntegral numelts))) | n <- zeroto numelts]
        LESA_Ptr     -> [pr bs segs (target_off + (fromIntegral n)) | n <- zeroto numelts]
        LESA_Composite sz -> [pr bs segs (target_off + (fromIntegral n * fromIntegral sz))
                             | n <- zeroto numelts]

--lesaFor :: { Int64 => (Int32, Int32) => ListEltSizeAlt };
lesaFor tag tagptr =
  case (tag, tagptr) of
    (0, _) -> LESA_Phantom
    (1, _) -> LESA_Bit
    (2, _) -> LESA_Byte1
    (3, _) -> LESA_Byte2
    (4, _) -> LESA_Byte4
    (5, _) -> LESA_Word
    (6, _) -> LESA_Ptr
    (7, (_, words)) -> LESA_Composite words
    _ -> error $ "unknown list size tag"

parseListPointerAt_ bs segs o =
  let w = bs `wordS` o in
  let (tag, w0) = splitU 2 w in
  case tag of
       0 ->
        if w == 0
          then
            (bs, o, LESA_Phantom, 0)
          else
            error $ "parseListPointerAt_ saw struct ptr instead    list ptr"
       1 ->
            let (b, w1) = splitS 30 w0 in
            let (c, w2) = splitU 3  w1 in
            let (d, w3) = splitU 29 w2 in

            let list_target_offset = fromIntegral b + o + 1 in
            let tagword = bs `wordS` list_target_offset in
            let tagptr = parseListTagPointer_ tagword in
            if c == 7
              then
                let (numelts, _) = tagptr in
                (bs, (list_target_offset + 1), (lesaFor c tagptr), numelts)
              else
                let numelts = d in
                (bs, (list_target_offset    ), (lesaFor c tagptr), numelts)

       2 ->
            let (b, w1) = splitU 1 w0 in
            let (c, w2) = splitU 29 w1 in
            let (d, w3) = splitU 32 w2 in
            if b == 0
              then let bs_ = lookupSegment segs (fromIntegral d) ("parseListPointerAt_ o=" ++ show o ++ "; w =" ++ showHex w "") in
                   parseListPointerAt_ bs_ segs (fromIntegral c)
              else error $ "parseListPointerAt_ can't yet support doubly-indirect pointers."
       _ -> 
            error $ "saw unknown ptr instead    list ptr"

parseListTagPointer_  w =
  let (_, w0) = splitU 2 w   in
  let (b, w1) = splitU 30 w0 in
  let (c, w2) = splitU 16 w1 in
  let (d, w3) = splitU 16 w2 in
  (fromIntegral b, fromIntegral (c + d))

readNthBitS bs boff n =
  let !(byteoff, bitoff) = (fromIntegral n) `divMod` 8 in
  readBitOfByte bitoff (boff + fromIntegral byteoff) bs
---------------------------------------------------------------------

wordLE :: (Integral a, Integral b, Bits b) => Int -> a -> a -> b
wordLE !n !a !b = let !x = shift (fromIntegral a) n
                      !y = fromIntegral b
                  in x .|. y

_w16 :: Word8 -> Word8 -> Word16
_w16 !a !b = wordLE 8 a b

_w32 :: Word16 -> Word16 -> Word32
_w32 !a !b = wordLE 16 a b

_w64 :: Word32 -> Word32 -> Word64
_w64 !a !b = wordLE 32 a b

bs8 :: Int64 -> ByteString -> Word8
bs8 !idx !bs = let !v = BS.index bs (fromIntegral idx) in v

bs16 :: Int64 -> ByteString -> Word16
bs16 !idx !bs = let !w0 = bs8 idx       bs in
                let !w1 = bs8 (idx + 1) bs in
                let !v = _w16 w1 w0 in
                v

bs32 :: Int64 -> ByteString -> Word32
bs32 !idx !bs = let !w0 = bs16 idx       bs in
                let !w1 = bs16 (idx + 2) bs in
                let !v = _w32 w1 w0 in
                v

bs64 :: Int64 -> ByteString -> Word64
bs64 !idx !bs = let !w0 = bs32 idx       bs in
                let !w1 = bs32 (idx + 4) bs in
                let !v = _w64 w1 w0 in
                v

bs8i :: Int64 -> ByteString -> Int8
bs8i idx bs = let !v = fromIntegral (bs8 idx bs) in v

bs16i :: Int64 -> ByteString -> Int16
bs16i idx bs = let !v = fromIntegral (bs16 idx bs) in v

bs32i :: Int64 -> ByteString -> Int32
bs32i idx bs = let !v = fromIntegral (bs32 idx bs) in v

bs64i :: Int64 -> ByteString -> Int64
bs64i idx bs = let !v = fromIntegral (bs64 idx bs) in v

bsvoid _bs = ()

bs1b :: Int64 -> ByteString -> Bool
bs1b !offset !bs =
  let !(byteoffset, bitoffset) = offset `divMod` 8 in
  let !v = bs8 byteoffset bs in
  testBit v (fromIntegral bitoffset)

isEven n = (n `mod` 2) == 0

plusOffset :: Offset -> Offset -> Offset
plusOffset = (+)

mulOffset :: Offset -> Offset -> Offset
mulOffset = (*)

wordS :: ByteString -> Int64 -> Word64
wordS !bs !nw = bs64 (8 * nw) bs

word :: ByteString -> Int64 -> Word64
word !bs !nw =                bs64 (8 * nw) bs

byte !bs !nb = fromIntegral $ bs8  nb bs

slice !off !len !bs = BS.take (fromIntegral len) (BS.drop (fromIntegral off) bs)
sliceWords !off !len !bs = slice (8 * off) (8 * len) bs

mask n = ((shift 1 n) - 1)

splitU :: Int -> Word64 -> (Word64, Word64)
splitU n w = (w .&. mask n, shiftR w n)

splitS :: Int -> Word64 -> (Int64, Word64)
splitS n w = let (u, r) = splitU n w in
             if testBit u (n - 1)
               then (- (fromIntegral $ clearBit u (n - 1)), r)
               else (   fromIntegral   u, r)

splitSegments rawbytes =
  let numsegs = (bs32 0 rawbytes) + 1 in
  let segsizes = [bs32 (4 * (fromIntegral n)) rawbytes | n <- [1..numsegs]] in
  -- If we have an odd number of segments, the the segment lengths plus the #segs word
  -- will end word-aligned; otherwise, we need an extra padding word.
  let startsegpos = 4 * (1 + fromIntegral numsegs + (if isEven numsegs then 1 else 0)) in
  let allsegbytes = BS.drop startsegpos rawbytes in
  let segoffsets = scanl (+) 0 segsizes in
  let !segs = [sliceWords offset len allsegbytes | (offset, len) <- zip segoffsets segsizes] in
  {-
  trace ("seg sizes: " ++ show segsizes ++ " (words), " ++ show (map (8*) segsizes) ++ " (bytes)"
          ++ "\n;; offsets/sizes in words: " ++ show (zip segoffsets segsizes)
          ++ "\n;; segment lengths in bytes: " ++ show (map BS.length segs)
          ++ " summing to " ++ show (sum (map BS.length segs))
          ++ "\n;; input bytes length " ++ show (BS.length rawbytes)) $
          -}
    segs

data Pointer = StructPtr !ByteString !String     !Int64 !Word64      !Word64 -- PointsInto, Origin, Offset, # data words, # ptr words
             | ListPtr   !ByteString !Int64 !Int64 !ListEltSize !Word64 -- PointsInto, Origin, Offset, eltsize, # elts
             | InvalidPtr String Int64

instance Show Pointer where
  show (StructPtr _ _ off ndw npw) = "(StructPtr " ++ show ndw ++ " " ++ show npw ++ ")"
  show (ListPtr   _ orig off eltsz nelts) = "(ListPtr " ++ show orig ++ " " ++ show off ++ " " ++ show nelts ++ " " ++ show eltsz ++ ")"
  show (InvalidPtr orig  off ) = "(InvalidPtr " ++ show orig ++ " " ++ show off ++ ")"

data FlatObj = StructFlat !ByteString ![Pointer]
             | ListFlat   ![FlatObj]    Pointer
             | StrFlat    !String
             | BytesFlat  !ByteString
             | InvalidFlat String
             deriving Show

data Object = StructObj  !ByteString ![Object]
            | ListObj    ![Object]      Pointer
            | StrObj     !String
            | BytesObj   !ByteString
            | InvalidObj !String
             deriving Show

dropLastChar str =    take (   length str - 1) str
dropLastByte bs  = BS.take (BS.length bs  - 1) bs

unText :: Object -> (ByteString, ())
unText (BytesObj bs) = (dropLastByte bs, ()) -- drop last byte
unText obj = (T.encodeUtf8 (T.pack $ unStrObj obj), ())

unStrObj :: Object -> String
unStrObj (StrObj str) = dropLastChar str
unStrObj (BytesObj bs) = T.unpack $ T.decodeUtf8 (dropLastByte bs)
unStrObj (StructObj bs []) | BS.null bs = ""
unStrObj other = error $ "unStrObj wasn't expecting " ++ show other

unBytes :: Object -> ByteString
unBytes (BytesObj bs) = bs
unBytes obj = error $ "unBytes of " ++ show obj

mk_void :: Object -> ()
mk_void _ = ()

mk_Bool :: Object -> Bool
mk_Bool (StrObj "0") = False
mk_Bool (StrObj "1") = True
mk_Bool o = error $ "mk_bool: " ++ show o

mk_Float64 :: Object -> Double
mk_Float64 (BytesObj bs) = wordToDouble (bs64 0 bs)
mk_Word64 :: Object -> Word64
mk_Word64 (BytesObj bs) = bs64 0 bs
mk_Word32 :: Object -> Word32
mk_Word32 (BytesObj bs) = bs32 0 bs
mk_Word16 :: Object -> Word16
mk_Word16 (BytesObj bs) = bs16 0 bs
mk_Word8 :: Object -> Word8
mk_Word8 (BytesObj bs) = bs8 0 bs

mk_Int64 :: Object -> Int64
mk_Int64 (BytesObj bs) = bs64i 0 bs
mk_Int32 :: Object -> Int32
mk_Int32 (BytesObj bs) = bs32i 0 bs
mk_Int16 :: Object -> Int16
mk_Int16 (BytesObj bs) = bs16i 0 bs
mk_Int8 :: Object -> Int8
mk_Int8 (BytesObj bs) = bs8i 0 bs

instance Pretty Object where
  pretty (StructObj bs    []     ) | BS.null bs = text "{{}}"
  pretty (ListObj         []   _ ) = text "{[]}"
  pretty (StructObj bs    objects) = parens $ text "StructObj" <$> indent 4 (text $ show bs)
                                                               <$> indent 4 (pretty objects)
  pretty (ListObj         objects _) = parens $ text "ListObj"   <+> indent 4 (pretty objects)
  pretty (InvalidObj          str) = parens $ text "InvalidObj:" <+> text str
  pretty (StrObj              str) = text (show str)

parseUnknownPointerAt :: String -> ByteString -> [ByteString] -> Int64 -> Pointer
parseUnknownPointerAt msg bs segs o =
 --trace ("parseUnknownPointerAt " ++ show o ++ " " ++ msg) $
  let !w = bs `word` o in
  let !(ptrtag, _) = splitU 2 w in
  case ptrtag of
    0 -> parseStructPointerAt bs o
    1 -> parseListPointerAt bs o
    2 -> parseInterSegmentPointerAt bs segs o
    _ -> error $ "parseUnknownPointer: " ++ show ptrtag ++ " At: " ++ show o

parseStructPointerAt :: ByteString -> Int64 -> Pointer
parseStructPointerAt bs o =
  let !w = bs `word` o in
  let !(_a, w0) = splitU 2 w in
  let !(!b, w1) = splitS 30 w0 in
  let !(!c, w2) = splitU 16 w1 in
  let !(!d, w3) = splitU 16 w2 in
  StructPtr bs (show o) (b + o + 1) c d

w2i :: Word64 -> Int64
w2i = fromIntegral

derefStructPointer :: Pointer -> [ByteString] -> FlatObj
derefStructPointer (StructPtr bs origin off numdata numptrs) segs =
  StructFlat (sliceWords off numdata bs)
             [parseUnknownPointerAt ("fromstruct@" ++ origin) bs segs (off + (w2i n))
               | n <- numdata `upby` numptrs]

readUnknownPointerAt o bs segs = derefUnknownPointer segs (parseUnknownPointerAt "readUnknownPointerAt" bs segs o)

parseListTagPointerAt :: ByteString -> Int64 -> (Word64, Word64, Word64)
parseListTagPointerAt bs o =
  let !w = bs `word` o in
  let !(_a, w0) = splitU 2 w in
  let !(!b, w1) = splitU 30 w0 in -- number of elements in the list
  let !(!c, w2) = splitU 16 w1 in -- # data words, per elt.
  let !(!d, w3) = splitU 16 w2 in -- # ptr  words, per elt.
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

parseListPointerAt :: ByteString -> Int64 -> Pointer
parseListPointerAt bs o =
  let !w = bs `word` o in
  let !(_a, w0) = splitU 2 w in
  let !(!b, w1) = splitS 30 w0 in
  let !(!c, w2) = splitU 3  w1 in
  let !(!d, w3) = splitU 29 w2 in
  let !list_target_offset = b + o + 1 in
  let !tagptr = parseListTagPointerAt bs list_target_offset in
  let !numelts = if c == 7 then let (ne, _, _) = tagptr in ne else d in
  -- b is the "Offset, in words, from the end of the pointer to the
  -- start of the first element in the list. Signed."
  --trace ("list ptr @ " ++ show o ++ " had b=" ++ show b) $
   ListPtr bs o (list_target_offset + (if c == 7 then 1 else 0)) (lesFor c tagptr) numelts

zeroto n =
  if n > 0 then [0 .. fromIntegral (n - 1)]
           else []

upby k n = map (+k) (zeroto n)

byteOffsetOf o = o * 8

charOfBool b = if b then '1' else '0'

readNthBit bs boff n =
  let !(byteoff, bitoff) = (fromIntegral n) `divMod` 8 in
  readBitOfByte bitoff (boff + fromIntegral byteoff) bs

readBitOfByte :: Int64 -> Int64 -> ByteString -> Bool
readBitOfByte bit byt bs =
  let !mask = (shiftL 1 (fromIntegral bit)) :: Int64 in
  ((byte bs byt) .&. mask) == mask

derefListPointer :: Pointer -> [ByteString] -> FlatObj
derefListPointer ptr@(ListPtr bs origin off eltsize numelts) segs =
  let !boff = byteOffsetOf off in
  case eltsize of
    LES_Phantom -> ListFlat (replicate (fromIntegral numelts) (StructFlat BS.empty [])) ptr
    LES_Bit     -> ListFlat [StrFlat [charOfBool (readNthBit bs boff n)] | n <- zeroto numelts] ptr
    LES_Byte1   -> BytesFlat (slice boff numelts bs)
    LES_Byte2   -> ListFlat [BytesFlat (slice (8 * off + 2 * n) 2 bs) | n <- zeroto numelts] ptr
    LES_Byte4   -> ListFlat [BytesFlat (slice (8 * off + 4 * n) 4 bs) | n <- zeroto numelts] ptr
    LES_Word    -> ListFlat [BytesFlat (sliceWords (off + n) 1 bs)    | n <- zeroto numelts] ptr
    LES_Ptr     -> ListFlat [derefUnknownPointer segs (parseUnknownPointerAt "derefListPtr" bs segs
                                                            (off + n)) | n <- zeroto numelts] ptr
    LES_Composite dw pw ->
      let offsets = [off + (fromIntegral $ i * (dw + pw)) | i <- zeroto numelts] in
      ListFlat [derefStructPointer (StructPtr bs ("LES_Composite: " ++ show ptr ++ ";" ++ show off') off' dw pw) segs | off' <- offsets] ptr

lookupSegment segs idx msg =
  if idx < length segs
    then segs !! idx
    else error $ "Minuproto.hs: lookupSegment cannot get " ++ show idx ++ "'th out of " ++ show (length segs) ++ " segments." ++ "\n" ++ msg

lookupPointer ptrs idx =
  if idx < length ptrs
    then ptrs !! idx
    else error $ "Minuproto.hs: lookupPointer cannot get " ++ show idx ++ "'th out of " ++ show (length ptrs) ++ " pointers."

parseInterSegmentPointerAt :: ByteString -> [ByteString] -> Int64 -> Pointer
parseInterSegmentPointerAt bs segs o =
  let !w = bs `word` o in
  let !(_a, w0) = splitU 2 w in
  let !(!b, w1) = splitU 1 w0 in
  let !(!c, w2) = splitU 29 w1 in
  let !(!d, w3) = splitU 32 w2 in
  if b == 0
    then let bs' = lookupSegment segs (fromIntegral d) ("parseInterSegmentPointerAt o=" ++ show o ++ "; w=" ++ showHex w "") in
         let pp = parseUnknownPointerAt "<<parseInterSegmentPointerAt>>" bs' segs (fromIntegral c) in
         -- trace ("parseInterSegmentPointerAt " ++ show o ++ "; " ++ show d ++ " " ++ show pp) $ pp
         pp
    else InvalidPtr ("parseInterSegmentPointerAt can't yet support doubly-indirect pointers. " ++ show o ++ " : " ++ showHex w "" ++ " //@902 " ++ show (bs `word` 902)) o

unflatten :: Int -> [ByteString] -> FlatObj -> Object
unflatten 0 _ flat = InvalidObj $ "no gas left for " ++ show flat
unflatten n segs (StructFlat words ptrs) = StructObj words (map (derefUnknownPointer' (n - 1) segs) ptrs)
unflatten n segs (ListFlat   flats p) =       ListObj       (map (unflatten (n - 1) segs) flats) p
unflatten _ _    (StrFlat    str)   =         StrObj str
unflatten _ _    (BytesFlat  bs )   =       BytesObj bs
unflatten _ _    (InvalidFlat str)  =      InvalidObj str

derefUnknownPointer :: [ByteString] -> Pointer -> FlatObj
derefUnknownPointer segs ptr =
  case ptr of
    StructPtr {} -> derefStructPointer ptr segs
    ListPtr   {} -> derefListPointer   ptr segs
    InvalidPtr str _ -> InvalidFlat str

derefUnknownPointer' :: Int -> [ByteString] -> Pointer -> Object
derefUnknownPointer' n segs ptr =
  unflatten n segs $ derefUnknownPointer segs ptr

parseSegment :: ByteString -> [ByteString] -> Object
parseSegment bs segs =
  unflatten 99999 segs $ readUnknownPointerAt 0 bs segs

parseBytes rawbytes =
  let segments@(seg:_) = splitSegments rawbytes in
  let obj = parseSegment seg segments in
  obj

instance Pretty Word64 where pretty w = text (show w)

roundUpToNextMultipleOf8 k = (k + 7) .&. (complement 7)

updateNextOffset :: ResizableArrayBuilder -> Offset -> IO Offset
updateNextOffset rab prevoffset = do
  nextoffset <- rabSize rab
  return $ max prevoffset (roundUpToNextMultipleOf8 $ fromIntegral nextoffset)

mapL :: (Object -> t) -> Object -> [t]
mapL f (ListObj vals _) = map f vals
mapL _ (StructObj bs []) | BS.null bs = []
mapL _ (StrObj "") = []
mapL f other = error $ "mapL can't map over " ++ show (pretty other) ++ " which is " ++ show other

delta_in_words bo1 bo2 = (bo1 - bo2) `div` 8

sr_list_of_Type_Float64 vals rab ptr_off data_off = sr_list_of_NonPtr vals rab 5 8 ptr_off data_off sr_Type_Float64
sr_list_of_Type_UInt64 vals rab ptr_off data_off = sr_list_of_NonPtr vals rab 5 8 ptr_off data_off sr_Type_UInt64
sr_list_of_Type_UInt32 vals rab ptr_off data_off = sr_list_of_NonPtr vals rab 4 4 ptr_off data_off sr_Type_UInt32
sr_list_of_Type_UInt16 vals rab ptr_off data_off = sr_list_of_NonPtr vals rab 3 2 ptr_off data_off sr_Type_UInt16
sr_list_of_Type_UInt8  vals rab ptr_off data_off = sr_list_of_NonPtr vals rab 2 1 ptr_off data_off sr_Type_UInt8
sr_list_of_Type_Int64  vals rab ptr_off data_off = sr_list_of_NonPtr vals rab 5 8 ptr_off data_off sr_Type_Int64
sr_list_of_Type_Int32  vals rab ptr_off data_off = sr_list_of_NonPtr vals rab 4 4 ptr_off data_off sr_Type_Int32
sr_list_of_Type_Int16  vals rab ptr_off data_off = sr_list_of_NonPtr vals rab 3 2 ptr_off data_off sr_Type_Int16
sr_list_of_Type_Int8   vals rab ptr_off data_off = sr_list_of_NonPtr vals rab 2 1 ptr_off data_off sr_Type_Int8

sr_list_of_NonPtr vals rab size_tag size_in_bytes ptr_off data_off sr_helper = do
  sr_ptr_list rab ptr_off size_tag (fromIntegral $ length vals) (delta_in_words data_off (ptr_off + 8))
  go vals data_off
    where go [] _ = if size_in_bytes == 8 then return () else rabPadToAlignment rab 8
          go (w:rest) !off = do sr_helper rab w off
                                go rest (off + size_in_bytes)

sr_list_of_Type_Text texts rab ptr_off data_off = do
  let !num_txt_ptrs = fromIntegral $ length texts
  sr_ptr_list rab ptr_off 6 num_txt_ptrs (delta_in_words data_off (ptr_off + 8))
  go texts data_off (data_off + (8 * num_txt_ptrs))
    where go []           _    _     = return ()
          go (text:rest) !poff !doff = do nwritten <- sr_Type_Text' text rab poff doff
                                          go rest (poff + 8) (doff + fromIntegral nwritten)

sr_list_of_Type_Bool bools rab ptr_off data_off = do
  sr_ptr_list rab ptr_off 1 (fromIntegral $ length bools) (delta_in_words data_off (ptr_off + 8))
  let byts = bytes_of_bools bools
  rabWriteBytes rab data_off $ BS.pack $ byts
  rabPadToAlignment rab 8
    where
      bytes_of_bools :: [Bool] -> [Word8]
      bytes_of_bools bools = go bools [] where
        go bools acc =
          case splitAt 8 bools of
            ([],      _)   -> reverse acc
            (first8, rest) -> go rest (byte_of_bools first8:acc)

      byte_of_bools :: [Bool] -> Word8
      byte_of_bools first8 =
        fromIntegral $ sum [2^k * (if d then 1 else 0)
                          | (k,d) <- zip [0..] first8]

sr_list_of_Type_Void voids rab ptr_off data_off = do
  sr_ptr_list rab ptr_off 0 (fromIntegral $ length voids) (delta_in_words data_off (ptr_off + 8))

sr_Type_Float64 rab val data_off = rabWriteWord64 rab data_off (doubleToWord val)

sr_Type_UInt8  rab val data_off = rabWriteWord8  rab data_off val
sr_Type_UInt16 rab val data_off = rabWriteWord16 rab data_off val
sr_Type_UInt32 rab val data_off = rabWriteWord32 rab data_off val
sr_Type_UInt64 rab val data_off = rabWriteWord64 rab data_off val
sr_Type_Int8   rab val data_off = rabWriteInt8   rab data_off val
sr_Type_Int16  rab val data_off = rabWriteInt16  rab data_off val
sr_Type_Int32  rab val data_off = rabWriteInt32  rab data_off val
sr_Type_Int64  rab val data_off = rabWriteInt64  rab data_off val

sr_Type_Void :: ResizableArrayBuilder -> () -> Offset -> IO ()
sr_Type_Void rab _unit _data_off = return ()

sr_Type_Bool :: ResizableArrayBuilder -> Bool -> Offset -> Int -> IO ()
sr_Type_Bool rab b data_off bit_off = do
  rabWriteBit rab data_off bit_off b

sr_Type_Data :: ByteString -> ResizableArrayBuilder -> Offset -> Offset -> IO ()
sr_Type_Data !val !rab !ptr_off !data_off = do
  rabWriteBytes rab data_off val
  sr_ptr_list rab ptr_off 2 (fromIntegral $ BS.length val) (delta_in_words data_off (ptr_off + 8))

padbyte_offsets o n = [o.. o + n]

isDefaultObj (StructObj bs []) = BS.length bs == 0
isDefaultObj (ListObj      [] _) = True
isDefaultObj _ = False

_mkMaybe :: (Object -> a) -> Object -> StrictMaybe a
_mkMaybe mk obj =
  if isDefaultObj obj
    then StrictlyNone
    else StrictlyJust (mk obj)

sr_Maybe !sr !mb_val !rab !ptr_off !data_off =
  case mb_val of
    StrictlyNone     -> return ()
    StrictlyJust val -> sr val rab ptr_off data_off

debugStr s = if False then putStrLn s else return ()

sr_Type_Text :: (ByteString, ()) -> ResizableArrayBuilder -> Offset -> Offset -> IO ()
sr_Type_Text !text !rab !ptr_off !data_off = do
  _ <- sr_Type_Text' text rab  ptr_off  data_off
  return ()

-- Returns number of *bytes* written, including nul/padding bytes.
sr_Type_Text' :: (ByteString, ()) -> ResizableArrayBuilder -> Offset -> Offset -> IO Int
sr_Type_Text' !(utf8, _txt) !rab !ptr_off !data_off = do
    let !o = data_off + fromIntegral (BS.length utf8)
    let !num_elts = BS.length utf8 + 1
    let !num_pad_bytes = let excess = num_elts `mod` 8 in
                          if excess == 0 then 0 else 8 - excess
    --putStrLn $ "serializing text of length " ++ show num_elts ++ " (incl. null terminator), with # padding bytes = " ++ show num_pad_bytes ++ " ::: " ++ show (padbyte_offsets o (fromIntegral num_pad_bytes))
    --putStrLn $ "text ptr is at " ++ show ptr_off ++ " and text data is at " ++ show data_off
    --bp <- rabSize rab
    --putStrLn $ "before padding, nextoffset will be " ++ show bp
    -- always writes at least one byte for nul terminator.
    rabWriteBytes rab data_off utf8
    mapM_ (\o -> do rabWriteWord8 rab o 0x00) (padbyte_offsets o (fromIntegral num_pad_bytes))

    --bp <- rabSize rab
    --putStrLn $ "after padding, nextoffset will be " ++ show bp
    sr_ptr_list rab ptr_off 2 (fromIntegral num_elts) (delta_in_words data_off (ptr_off + 8))
    return (num_elts + num_pad_bytes)

sr_ptr_list :: ResizableArrayBuilder -> Offset -> Int -> Offset -> Offset -> IO ()
sr_ptr_list !rab !ptr_off !size_tag !num_elts_or_words !delta = do
      let a_tag = 1
      --putStrLn $ "emitting list ptr @ " ++ show ptr_off ++ " with tag/nelts/delta = " ++ show (size_tag, num_elts_or_words, delta) ++ " ; " ++ show ((fromIntegral size_tag + fromIntegral num_elts_or_words `shiftL` 3) :: Word32)
      rabWriteWord32 rab  ptr_off      (a_tag + (fromIntegral delta `shiftL` 2))
      rabWriteWord32 rab (ptr_off + 4) (fromIntegral size_tag + (fromIntegral num_elts_or_words `shiftL` 3)) -- size in bytes = # words << 3

sr_ptr_struct :: ResizableArrayBuilder -> Offset -> Word16 -> Word16 -> Offset -> IO ()
sr_ptr_struct !rab !ptr_off !sizedata !sizeptrs !delta = do
  rabWriteWord32 rab  ptr_off     (fromIntegral delta `shiftL` 2)
  rabWriteWord16 rab (ptr_off + 4) sizedata
  rabWriteWord16 rab (ptr_off + 6) sizeptrs

sr_composite_list_helper :: ResizableArrayBuilder -> Offset -> Offset -> Offset -> [s]
                         -> (s -> ResizableArrayBuilder -> Offset -> Offset -> IO ())
                         -> IO ()
sr_composite_list_helper !rab !objsize_bytes !base_target_off !base_ser_off !objs !helper = do
  let ser nextoffset (n, obj) = do
        let !target_off = base_target_off + (objsize_bytes * n)
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

serializeWith :: a -> (a -> ResizableArrayBuilder -> Offset -> Offset -> IO ()) -> IO ByteString
serializeWith obj serializer = do
  rab <- newResizableArrayBuilder
  serializer obj rab 0 8 -- ptr offset, data offset
  rabPadToAlignment rab 8
  bs <- rabToByteString rab
  return $ frameCapnProtoMessage bs

-- According to https://capnproto.org/encoding.html#serialization-over-a-stream
-- the framing format is:
--   4 bytes: number of segments, minus one
--   4 bytes * N: size of each segment, in words
--   0 or 4 bytes: padding (if N is even)
--   contents of all frames
frameCapnProtoMessage :: ByteString -> ByteString
frameCapnProtoMessage bs =
  let frame = BD.byteString bs in
    LBS.toStrict $ BD.toLazyByteString $
      BD.word32LE 0 `mappend` BD.word32LE (fromIntegral (BS.length bs `div` 8)) `mappend` frame

