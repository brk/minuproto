module Main where

import Data.Int
import Data.Bits
import Data.Word
import qualified Data.ByteString as BS
import Data.ByteString(ByteString)
import Data.Char(chr)
import Data.List((!!))

import Text.PrettyPrint.ANSI.Leijen

import Debug.Trace(trace)

wordLE n a b = let cast = fromInteger . toInteger in
               shift (cast a) n .|. cast b

w16 :: Word8 -> Word8 -> Word16
w16 a b = wordLE 8 a b

w32 :: Word16 -> Word16 -> Word32
w32 a b = wordLE 16 a b

w64 :: Word32 -> Word32 -> Word64
w64 a b = wordLE 32 a b

bs8 :: ByteString -> (Word8, ByteString)
bs8 bs = case BS.uncons bs of
          Just res -> res
          Nothing -> (0, bs)

bs16 :: ByteString -> (Word16, ByteString)
bs16 bs0 = let (w0, bs1) = bs8 bs0 in
           let (w1, bs2) = bs8 bs1 in
           (w16 w1 w0, bs2)

bs32 :: ByteString -> (Word32, ByteString)
bs32 bs0 = let (w0, bs1) = bs16 bs0 in
           let (w1, bs2) = bs16 bs1 in
           (w32 w1 w0, bs2)

bs64 :: ByteString -> (Word64, ByteString)
bs64 bs0 = let (w0, bs1) = bs32 bs0 in
           let (w1, bs2) = bs32 bs1 in
           (w64 w1 w0, bs2)

at :: (ByteString -> (word, ByteString)) -> Int64 -> ByteString -> word
at f n bs = let (v, _) = f (BS.drop (fromIntegral n) bs) in v

isOdd n = (n `mod` 2) == 0

newtype WordOffset = WordOffset { unWordOffset :: Int64 } deriving (Show, Eq, Ord)
newtype ByteOffset = ByteOffset Int64 deriving (Show, Eq, Ord)

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
byt4 bs (ByteOffset nb) = fromIntegral $ at bs8  nb bs

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
  [sliceWords offset len allsegbytes | (offset, len) <- zip segoffsets segsizes]

--type Pointer = (Int64, Word64, Word64)
data Pointer = StructPtr String WordOffset Word64      Word64 -- Origin, Offset, # data words, # ptr words
             | ListPtr   WordOffset WordOffset ListEltSize Word64 -- Origin, Offset, eltsize, # elts
             | InvalidPtr
             deriving Show

data FlatObj = StructFlat ByteString [Pointer]
             | ListFlat   [FlatObj]
             | StrFlat    String
             | InvalidFlat
             deriving Show

data Object = StructObj ByteString [Object]
            | ListObj   [Object]
            | StrObj     String
            | InvalidObj String
             deriving Show

unStrObj (StrObj str) = str

instance Pretty Object where
  pretty (StructObj bs    []     ) | BS.null bs = text "{{}}"
  pretty (ListObj         []     ) = text "{[]}"
  pretty (StructObj bs    objects) = parens $ text "StructObj" <$> indent 4 (text $ show bs)
                                                               <$> indent 4 (pretty objects)
  pretty (ListObj         objects) = parens $ text "ListObj"   <+> indent 4 (pretty objects)
  pretty (InvalidObj          str) = parens $ text "InvalidObj:" <+> text str
  pretty (StrObj              str) = text (show str)

parseUnknownPointerAt :: String -> ByteString -> WordOffset -> Pointer
parseUnknownPointerAt msg bs o =
 --trace ("parseUnknownPointerAt " ++ show o ++ " " ++ msg) $
  let w = bs `word` o in
  let (ptrtag, _) = splitU 2 w in
  case ptrtag of
    0 -> parseStructPointerAt bs o
    1 -> parseListPointerAt bs o
    2 -> error $ "parseInterSegmentPointerAt bs " ++ show o
    _ -> -- error $ "parseUnknownPointer: " ++ show ptrtag ++ " At: " ++ show o
          InvalidPtr

parseStructPointerAt :: ByteString -> WordOffset -> Pointer
parseStructPointerAt bs o =
  let w = bs `word` o in
  let (_a, w0) = splitU 2 w in
  let ( b, w1) = splitS 30 w0 in
  let ( c, w2) = splitU 16 w1 in
  let ( d, w3) = splitU 16 w2 in
  StructPtr (show o) (WordOffset b + o + 1) c d

w2i :: Word64 -> Int64
w2i = fromIntegral

derefStructPointer :: Pointer -> ByteString -> FlatObj
derefStructPointer (StructPtr origin off numdata numptrs) bs =
  StructFlat (sliceWords (unWordOffset off) numdata bs)
             [parseUnknownPointerAt ("fromstruct@" ++ origin) bs (off + WordOffset (w2i n))
               | n <- numdata `upby` numptrs]

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
   ListPtr o (list_target_offset + (if c == 7 then 1 else 0)) (lesFor c tagptr) numelts

zeroto n =
  if n > 0 then [0 .. fromIntegral (n - 1)]
           else []

upby k n = map (+k) (zeroto n)

byteOffsetOf (WordOffset o) = o * 8

derefListPointer :: Pointer -> ByteString -> FlatObj
derefListPointer ptr@(ListPtr origin off eltsize numelts) bs =
  let boff = byteOffsetOf off in
  case eltsize of
    LES_Phantom -> ListFlat (replicate (fromIntegral numelts) (StructFlat BS.empty []))
    LES_Byte1   -> StrFlat [chr $ fromIntegral $ byte bs (ByteOffset $ boff + n) | n <- zeroto numelts]
    --LES_Byte4   -> ListFlat [StructFlat [byt4 bs (ByteOffset $ boff + 4 * n)] [] | n <- zeroto numelts]
    --LES_Word    -> ListFlat [StructFlat [word bs (off + WordOffset n)]        [] | n <- zeroto numelts]
    LES_Word    -> ListFlat [StructFlat (sliceWords (unWordOffset off + n) 1 bs)        [] | n <- zeroto numelts]
    LES_Composite dw pw ->
      let offsets = [off + (fromIntegral $ i * (dw + pw)) | i <- zeroto numelts] in
      ListFlat [derefStructPointer (StructPtr (show ptr ++ ";" ++ show off') off' dw pw) bs | off' <- offsets]
    _ -> error $ "can't yet parse list of elts sized " ++ show eltsize

unflatten :: Int -> ByteString -> FlatObj -> Object
unflatten 0 _ flat = InvalidObj $ "no gas left for " ++ show flat
unflatten n bs (StructFlat words ptrs) = StructObj words (map (derefUnknownPointers (n - 1) bs) ptrs)
unflatten n bs (ListFlat   flats) =        ListObj       (map (unflatten (n - 1) bs) flats)
unflatten _ _  (StrFlat    str)   =         StrObj str
unflatten n bs InvalidFlat = InvalidObj "unflatten invalid"

derefUnknownPointers :: Int -> ByteString -> Pointer -> Object
derefUnknownPointers n bs ptr =
  unflatten n bs $
    case ptr of
      StructPtr {} -> derefStructPointer ptr bs
      ListPtr   {} -> derefListPointer   ptr bs
      InvalidPtr {} -> InvalidFlat

parseSegment bs =
  let ptr = parseStructPointerAt bs 0 in
  unflatten 99999 bs $ derefStructPointer ptr bs

main = do
  rawbytes <- BS.readFile "person.schema.bin"
  let segments@(seg:_) = splitSegments rawbytes
  let obj = parseSegment seg
  --putDoc $ pretty obj <> line
  print $ mkCodeGeneratorRequest obj
  mapM (\x -> putStrLn "" >> print x) $ cgrNodes $ mkCodeGeneratorRequest obj

instance Pretty Word64 where pretty w = text (show w)

------------------------------------------------------------

data CodeGeneratorRequest = CodeGeneratorRequest {
    cgrNodes :: [Node]
  , cgrRequestedFiles :: [RequestedFile]
} deriving Show

data Node = Node { nodeId :: Word64
                 , nodeScopeId :: Word64
                 , nodeDisplayPrefix :: Word32
                 , nodeDisplayName :: String
                 , nodeUnion :: NodeUnion
} deriving Show

data NodeUnion =
     NodeStruct { nodeStruct_dataWordCount :: Word16
                , nodeStruct_pointerCount :: Word16
                , nodeStruct_preferredListEncoding :: Word16
                , nodeStruct_isGroup :: Word8
                , nodeStruct_discriminantCount :: Word16
                , nodeStruct_discriminantOffset :: Word16
                , nodeStruct_fields :: [Field]
                }
  | NodeEnum    { nodeEnum_enumerants :: [Enumerant] }
  | NodeInterface { nodeInterface_methods :: [Method] }
  | NodeConst   { nodeConst_type :: ()
                , nodeConst_value :: () }
  -- | NodeAnnotation { nodeAnnotation
  deriving Show

data Struct = Struct {

} deriving Show

data Field = Field {
      fieldName :: String
--  , fieldSlot :: ()
    , fieldCodeOrder :: Word16
    , fieldDiscriminant :: Word16
    , fieldUnion :: FieldUnion
} deriving Show

data FieldUnion =
     FieldSlot
   | FieldGroup
  deriving Show

data RequestedFile = RequestedFile {
      rfId   :: Word64
    , rfName :: String
} deriving Show

data Method = Method {
     methodName :: String
   , methodOrder :: Word16
} deriving Show

data Enumerant = Enumerant {
     enumerantName :: String
   , enumerantOrder :: Word16
} deriving Show

data Type_ =
     Type_Void
   | Type_Bool
   | Type_Int8
   | Type_Int16
   | Type_Int32
   | Type_Int64
   | Type_UInt8
   | Type_UInt32
   | Type_UInt64
   | Type_Float32
   | Type_Float64
   | Type_Text
   | Type_Data
   | Type_List       Type_
   | Type_Enum       Word64
   | Type_Struct     Word64
   | Type_Interface  Word64
   | Type_Object
deriving Show

data Value =
     Value_Void
   | Value_Bool     Bool
   | Value_Int8     Word8
   | Value_Int16    Word16
   | Value_Int32    Word32
   | Value_Int64    Word64
   | Value_UInt8    Word8
   | Value_UInt32   Word32
   | Value_UInt64   Word64
   | Value_Float32  Float
   | Value_Float64  Double
   | Value_Text     String
   | Value_Data     String
   | Value_List       
   | Value_Enum       Word16
   | Value_Struct     
   | Value_Interface  
   | Value_Object
deriving Show


mapL _ f (ListObj vals) = map f vals
mapL _ _ (StructObj bs []) | BS.null bs = []
mapL msg f other = error $ "mapL("++msg++") can't map over " ++ show (pretty other)

mkCodeGeneratorRequest :: Object -> CodeGeneratorRequest
mkCodeGeneratorRequest (StructObj _bs [nodes, reqfiles]) =
  CodeGeneratorRequest (mapL "cgr" mkNode nodes) (mapL "mkcg" mkRequestedFile reqfiles)

mkRequestedFile (StructObj bs [StrObj name, _imports]) = RequestedFile id name
  where id = at bs64 0 bs
mkRequestedFile other = error $ "mkRequestedFile " ++ show (pretty other)

mkNode          (StructObj bs
                           (StrObj displayName:
                            ListObj nestedNodes:
                            annotations:rest)) =
    Node id scopeId prefixLen displayName union
      where
          id        = at bs64  0 bs
          prefixLen = at bs32  8 bs
          which     = at bs16 12 bs
          scopeId   = at bs64 16 bs
          union     = case which of
                        0 -> NodeStruct (at bs16 14 bs)
                                        (at bs16 24 bs)
                                        (at bs16 26 bs)
                                        (at bs8  28 bs)
                                        (at bs16 30 bs)
                                        (at bs16 32 bs)
                                        (mapL "NodeFields" mkField (rest !! 0))
                        1 -> NodeEnum (mapL "NodeE" mkEnumerant (rest !! 0))
                        2 -> NodeInterface (mapL "NodeI" mkMethod (rest !! 0))
                        3 -> NodeConst (error "NodeConstType") (error "NodeConstValue")-- (rest !! 0) (rest !! 1)
                        4 -> error "NodeAnnotation"  -- NodeAnnotation (error "NodeAnnotation")
                        _ -> error "Unknown Node discriminant"

mkNode other = error $ "mkNode couldn't handle\n" ++ show (pretty other)

mkField  (StructObj bs (StrObj name:annotations:rest)) =
  Field name codeOrder discriminantValue t1
    where codeOrder = at bs16 0 bs
          discriminantValue = (at bs16 2 bs) `xor` 65535
          which = at bs16 8 bs
          t1 = case which of
                0 -> FieldSlot (at bs32 4)
                               (mkType  $ rest !! 0)
                               (mkValue $ rest !! 1)
                1 -> FieldGroup
                _ -> error "Field which1"

mkField other = error $ "mkField couldn't handle\n" ++ show (pretty other)



mkMethod (StructObj bs (StrObj name:rest)) =
  Method name (at bs16 0 bs)

mkEnumerant (StructObj bs (StrObj name:rest)) =
  Enumerant name (at bs16 0 bs)


