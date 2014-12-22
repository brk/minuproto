module MinuprotoBootstrap where

import Minuproto

import ResizableArrayBuilder

import Data.Int
import Data.Bits
import Data.Word
import qualified Data.ByteString as BS
import Data.ByteString(ByteString)
import Data.Binary.IEEE754(floatToWord, wordToFloat, doubleToWord, wordToDouble)

import Text.PrettyPrint.ANSI.Leijen

---------------------------------------------------------------------
-- Representation of schema.capnp as a hand-written Haskell datatype:

data CodeGeneratorRequest = CodeGeneratorRequest {
    cgrNodes :: [Node]
  , cgrRequestedFiles :: [RequestedFile]
} deriving Show

data Node = Node { nodeId :: Word64
                 , nodeScopeId :: Word64
                 , nodeDisplayPrefix :: Word32
                 , nodeDisplayName_ :: String
                 , nodeUnion :: NodeUnion
                 , nodeNestedNodes :: [NestedNode]
} deriving Show

data NestedNode =
     NestedNode { nestedNode_name :: String
                , nestedNode_id   :: Word64
     } deriving Show

data NodeUnion =
     NodeFile
   | NodeStruct { nodeStruct_dataWordCount :: Word16
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
  | NodeAnnotation { nodeAnnotation_type :: Type_
                   , nodeAnnotation_file :: Bool
                   , nodeAnnotation_const :: Bool
                   , nodeAnnotation_enum :: Bool
                   , nodeAnnotation_enumerant :: Bool
                   , nodeAnnotation_struct :: Bool
                   , nodeAnnotation_field :: Bool
                   , nodeAnnotation_union :: Bool
                   , nodeAnnotation_group :: Bool
                   , nodeAnnotation_interface :: Bool
                   , nodeAnnotation_method :: Bool
                   , nodeAnnotation_param :: Bool
                   , nodeAnnotation_annotation :: Bool
                   }
  deriving Show

data Field = Field {
      fieldName_ :: String
    , fieldCodeOrder :: Word16
    , fieldDiscriminant :: Word16
    , fieldUnion :: FieldUnion
    , fieldOrdinal :: FieldOrdinal
    , fieldAnnotations :: [Annotation]
} deriving Show

data Annotation = Annotation {
      annotationId :: Word64
    , annotationValue :: Value
} deriving Show

-- Magic constant: we require that the $optional annotation
-- be explicitly given a "known" id. Mostly so that this function
-- can be pure and not monadic. But a nice side effect is separating
-- the "syntax" (i.e. written-down name) from the semantic effect.
isOptionalAnnotation (Annotation id _) = id == 0xfdd8d84c51405f88

isFieldOptional f = any isOptionalAnnotation (fieldAnnotations f)

fieldName typename f = fieldName_ f ++ "_of_" ++ typename

data FieldUnion =
     FieldSlot  Word32 Type_ Value
   | FieldGroup Word64
  deriving Show

data FieldOrdinal =
     FieldOrdinalImplicit
   | FieldOrdinalExplicit Word16
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
   | Type_UInt16
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
   | Value_UInt16   Word16
   | Value_UInt32   Word32
   | Value_UInt64   Word64
   | Value_Float32  Float
   | Value_Float64  Double
   | Value_Text     String
   | Value_Data     String
   | Value_List       
   | Value_Enum     Word16
   | Value_Struct     
   | Value_Interface  
   | Value_Object   Object -- (from Minuproto.hs)
   | Value_ERROR
   deriving Show

data Kind = KindData | KindPtr deriving (Eq, Show)

---------------------------------------------------------------------
-- An assortment of pure helper functions:

byteSizeOfType :: Type_ -> Int
byteSizeOfType type_ =
    case type_ of
      Type_Void        -> 0
      Type_Bool        -> 1
      Type_Int8        -> 1
      Type_Int16       -> 2
      Type_Int32       -> 4
      Type_Int64       -> 8
      Type_UInt8       -> 1
      Type_UInt16      -> 2
      Type_UInt32      -> 4
      Type_UInt64      -> 8
      Type_Float32     -> 4
      Type_Float64     -> 8
      Type_Text        -> 8
      Type_Data        -> 8
      Type_List      _ -> 8
      Type_Enum      _ -> 2
      Type_Struct    _ -> 8
      Type_Interface _ -> 8
      Type_Object      -> 8

accessorNameForType :: Type_ -> String
accessorNameForType type_ =
    case type_ of
      Type_Void        -> "bsvoid"
      Type_Bool        -> "bs1b"
      Type_Int8        -> "bs8i"
      Type_Int16       -> "bs16i"
      Type_Int32       -> "bs32i"
      Type_Int64       -> "bs64i"
      Type_UInt8       -> "bs8"
      Type_UInt16      -> "bs16"
      Type_UInt32      -> "bs32"
      Type_UInt64      -> "bs64"
      Type_Float32     -> error $ "no accessor yet for " ++ show type_
      Type_Float64     -> error $ "no accessor yet for " ++ show type_
      Type_Text        -> error $ "no accessor yet for " ++ show type_
      Type_Data        -> error $ "no accessor yet for " ++ show type_
      Type_List      _ -> error $ "no accessor yet for " ++ show type_
      Type_Enum      _ -> "bs16"
      Type_Struct    _ -> error $ "no accessor yet for " ++ show type_
      Type_Interface _ -> error $ "no accessor yet for " ++ show type_
      Type_Object      -> error $ "no accessor yet for " ++ show type_

--------------------------------------------------------------
-- Transformation from generic parsed capnp AST representation
-- to CodeGeneratorRequest and friends.

mkCodeGeneratorRequest :: Object -> CodeGeneratorRequest
mkCodeGeneratorRequest (StructObj _bs [nodes, reqfiles]) =
  CodeGeneratorRequest (mapL mkNode nodes) (mapL mkRequestedFile reqfiles)
mkCodeGeneratorRequest other = error $ "mkCodeGeneratorRequest $ " ++ show other

mkRequestedFile (StructObj bs [name, _imports]) = RequestedFile id (unStrObj name)
  where id = at_ bs64 0 bs
mkRequestedFile other = error $ "mkRequestedFile " ++ show (pretty other)

mkNode          (StructObj bs
                           (displayNameStrObj:
                            nestedNodes:
                            annotations:rest)) =
    Node id scopeId prefixLen (unStrObj displayNameStrObj) union (mapL mkNestedNode nestedNodes)
      where
          id        = at_ bs64  0 bs
          prefixLen = at_ bs32  8 bs
          which     = at_ bs16 12 bs
          scopeId   = at_ bs64 16 bs
          union     = case which of
                        0 -> NodeFile
                        1 -> NodeStruct (at_ bs16 14 bs)
                                        (at_ bs16 24 bs)
                                        (at_ bs16 26 bs)
                                        (at_ bs8  28 bs)
                                        (at_ bs16 30 bs)
                                        (at_ bs16 32 bs)
                                        (mapL mkField (rest !! 0))
                        2 -> NodeEnum (mapL mkEnumerant (rest !! 0))
                        3 -> NodeInterface (mapL mkMethod (rest !! 0))
                        4 -> NodeConst (error "NodeConstType") (error "NodeConstValue")-- (rest !! 0) (rest !! 1)
                        5 -> NodeAnnotation (mkType $ rest !! 0)
                                            (readNthBit bs 14 0)
                                            (readNthBit bs 14 1)
                                            (readNthBit bs 14 2)
                                            (readNthBit bs 14 3)
                                            (readNthBit bs 14 4)
                                            (readNthBit bs 14 5)
                                            (readNthBit bs 14 6)
                                            (readNthBit bs 14 7)
                                            (readNthBit bs 14 8)
                                            (readNthBit bs 14 9)
                                            (readNthBit bs 14 10)
                                            (readNthBit bs 14 11)
                        v -> error $ "Unknown Node discriminant:" ++ show v

mkField  (StructObj bs (name:annotations:rest)) =
  Field (unStrObj name) codeOrder discriminantValue t1 explicit (mapL mkAnnotation annotations)
    where codeOrder = at_ bs16 0 bs
          discriminantValue = (at_ bs16 2 bs) `xor` (65535 :: Word16)
          which = at_ bs16 8 bs
          t1 = case which of
                0 -> FieldSlot (at_ bs32 4 bs)
                               (mkType  $ rest !! 0)
                               (mkValue $ rest !! 1)
                1 -> FieldGroup (at_ bs64 16 bs)
                _ -> error "Field which1"
          explicit = case at_ bs16 10 bs of
                       0 -> FieldOrdinalImplicit
                       1 -> FieldOrdinalExplicit (at_ bs16 12 bs)

mkField other = error $ "mkField couldn't handle\n" ++ show (pretty other)

mkType :: Object -> Type_
mkType (StructObj bs objs) =
  let which = at_ bs16 0 bs in
  case which of
    0  -> Type_Void
    1  -> Type_Bool
    2  -> Type_Int8
    3  -> Type_Int16
    4  -> Type_Int32
    5  -> Type_Int64
    6  -> Type_UInt8
    7  -> Type_UInt16
    8  -> Type_UInt32
    9  -> Type_UInt64
    10 -> Type_Float32
    11 -> Type_Float64
    12 -> Type_Text
    13 -> Type_Data
    14 -> Type_List       (mkType $ objs !! 0)
    15 -> Type_Enum       (at_ bs64 8 bs)
    16 -> Type_Struct     (at_ bs64 8 bs)
    17 -> Type_Interface  (at_ bs64 8 bs)
    18 -> Type_Object

mkValue :: Object -> Value
mkValue (StructObj bs objs) =
  let which = at_ bs16 0 bs in
  case which of
    0  -> Value_Void
    1  -> Value_Bool     (at_ bs8  2 bs `mod` 2 == 1)
    2  -> Value_Int8     (at_ bs8  2 bs)
    3  -> Value_Int16    (at_ bs16 2 bs)
    4  -> Value_Int32    (at_ bs32 2 bs)
    5  -> Value_Int64    (at_ bs64 2 bs)
    6  -> Value_UInt8    (at_ bs8  2 bs)
    7  -> Value_UInt16   (at_ bs16 2 bs)
    8  -> Value_UInt32   (at_ bs32 2 bs)
    9  -> Value_UInt64   (at_ bs64 2 bs)
    10 -> Value_Float32  (wordToFloat  $ at_ bs32 2 bs)
    11 -> Value_Float64  (wordToDouble $ at_ bs64 2 bs)
    12 -> Value_Text     (unStrObj $ objs !! 0)
    13 -> Value_Data     (unStrObj $ objs !! 0)
    14 -> Value_List       
    15 -> Value_Enum     (at_ bs16 2 bs)
    16 -> Value_Struct     
    17 -> Value_Interface  
    18 -> Value_Object   (objs !! 0)
    _  -> Value_ERROR

mkMethod (StructObj bs (name:rest)) =
  Method (unStrObj name) (at_ bs16 0 bs)

mkNestedNode (StructObj bs [name]) = NestedNode (unStrObj name) (at_ bs64 0 bs)

mkEnumerant (StructObj bs (name:rest)) =
  Enumerant (unStrObj name) (at_ bs16 0 bs)

mkAnnotation (StructObj bs (value:rest)) =
  Annotation (at_ bs64 0 bs)
             (mkValue value)

