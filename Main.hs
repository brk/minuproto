module Main where

import Minuproto
import ResizableArrayBuilder

import Data.Int
import Data.Bits
import Data.Word
import qualified Data.ByteString as BS
import Data.ByteString(ByteString)
import Data.Char(toUpper)
import Data.List((!!), foldl')
import Data.Binary.IEEE754(floatToWord, wordToFloat, doubleToWord, wordToDouble)

import Text.PrettyPrint.ANSI.Leijen

import Data.Map(Map)
import qualified Data.Map as Map

import Data.List(intersperse, isPrefixOf)

import Control.Monad.State
import System.IO(withFile, IOMode(WriteMode), stdout)

main = do
  rawbytes <- BS.readFile "testdata/test2.schema.bin"
  let segments@(seg:_) = splitSegments rawbytes
  let obj = parseSegment seg segments
  let cgr = mkCodeGeneratorRequest obj
  let hs_code_doc = evalState (cgHS cgr) (CG_State Map.empty Map.empty)
  modularizeAndPutDocToFile hs_code_doc (rfName ((cgrRequestedFiles cgr) !! 0))

------------------------------------------------------------
moduleNameOf str = capitalizeFirstLetter $ replaceWith '.' '_' str
replaceWith c r str = map (\v -> if v == c then r else v) str
------------------------------------------------------------
modularizeAndPutDocToFile d protoname =
  putDocToFile (vcat [ text "module" <+> text (moduleNameOf protoname) <+> text "where"
                     , text "import Data.ByteString(ByteString)"
                     , text "import Minuproto"
                     , text "import ResizableArrayBuilder"
                     , text "import Data.Word"
                     ] <$> d) (moduleNameOf protoname ++ ".hs")
------------------------------------------------------------
hPutDocWide h d = displayIO h (renderPretty 0.9 110 d)

putDocToFile d f = do
  withFile f WriteMode (\h -> hPutDocWide h d)
------------------------------------------------------------

data CG_State =
     CG_State (Map Word64 String) (Map Word64 Word16)

type CG t = State CG_State t

class CGHS t where
  cgHS :: t -> CG Doc

instance CGHS CodeGeneratorRequest where
  cgHS cgr = do
    -- Build the mapping of node ids to type names for later pretty-printing.
    mapM_ denoteNodeAttributes (cgrNodes cgr)
    -- Emit the data type declaration for each node.
    let productiveNodes = filter isNodeProductive (cgrNodes cgr)
    ns <- mapM cgHS productiveNodes
    -- Emit builders for each node.
    builders <- mapM emitNodeBuilder productiveNodes
    serializers <- mapM emitNodeSerializer productiveNodes
    return $ vsep $ ns ++ builders ++ serializers

isNodeProductive node =
  case nodeUnion node of
    NodeFile -> False
    NodeAnnotation {} -> False
    _ -> True

emitNodeSerializer node =
  emitNodeUnionSerializer (nodeUnion node) (nodeDisplayName node) (nodeId node)

splitFields fields =
  (filter (isSlotOfKind KindData) fields,
   filter (isSlotOfKind KindPtr)  fields)

isSlotOfKind k f =
  case fieldUnion f of
    FieldSlot _ t _ -> kindOfType t == k
    _ -> False

makerForType (Type_Enum   w) = text $ "mk_enum_"   ++ show w
makerForType (Type_Struct w) = text $ "mk_struct_" ++ show w
makerForType (Type_List (Type_Struct w)) = text $ "sr_list_of_" ++ show w
makerForType (Type_List (Type_Enum   w)) = text $ "sr_list_of_" ++ show w
makerForType (Type_List t) = text $ "sr_list_of_" ++ show t
makerForType t = text ("sr_" ++ show t)

serializerForType (Type_Enum   w) = text $ "sr_enum_"   ++ show w
serializerForType (Type_Struct w) = text $ "sr_struct_" ++ show w
serializerForType (Type_List (Type_Struct w)) = text $ "sr_list_of_" ++ show w
serializerForType (Type_List (Type_Enum   w)) = text $ "sr_list_of_" ++ show w
serializerForType (Type_List t) = text $ "sr_list_of_" ++ show t
serializerForType t = text ("sr_" ++ show t)

serializerForGroup w = text $ "sr_group_" ++ show w

helperForStructSerializer nodeid = "sr_struct_helper_" ++ show nodeid

quoted d = squote <> d <> squote
quotedStr s = quoted (text s)

-- {{{ Haskell syntax details
match var arms =
  text "case" <+> text var <+> text "of"
  <$> indent 2 (vcat [pat <+> text "->" <+> body | (pat, body) <- arms])

doblock stmts = text "do" <$> indent 2 (vcat stmts)

srCall strs = txCall (map text strs)
txCall txts = parens (foldl1 (<+>) (         txts))

multiLineComment doc = vsep [text "{-", doc, text "-}"]
lineComment doc = text "--" <+> doc

emitListIndex nm off = srCall ["(!!)", nm, show off]

emitAdd s1 s2 = srCall [s1, "+", s2]

fnDefinition name args argtypes retty body =
  let defn = name <+> hsep args <+> text "=" <+> body <$> text "" in
  let decl = name <+> text "::" <+> encloseSep empty empty (text " -> ") (argtypes ++ [retty]) in
  case argtypes of
    [] ->          defn
    _  -> decl <$> defn
-- }}}

instance Pretty Word16 where pretty w = text (show w)
instance Pretty Word32 where pretty w = text (show w)
instance Pretty Type_  where pretty w = text (show w)

getFieldAccessor f =
  if fieldDiscriminant f /= 0xffff
    then fieldUnCtorName f
    else fieldName f

-- Individual bits must be specially serialized, because their offsets
-- are measured in bits, not bytes.
emitFieldSerializer f | (FieldSlot offsetInBits Type_Bool _) <- fieldUnion f =
  (txCall [serializerForType Type_Bool, text "rab", srCall [getFieldAccessor f, "obj"],
           text "data_off", pretty offsetInBits])
     <+> lineComment (text "serialize bool field" <+> quotedStr (fieldName_ f))

emitFieldSerializer f | (FieldSlot w t _) <- fieldUnion f =
  let offsetInBytes = fromIntegral w * byteSizeOfType t in
  (case kindOfType t of
    KindPtr ->
      txCall [serializerForType t, srCall [getFieldAccessor f, "obj"],
                     text "rab",  (emitAdd "ptrs_off" (show offsetInBytes)), text "nextoffset"]
      <$> text "nextoffset <- updateNextOffset rab nextoffset ; return ()"
    KindData ->
      txCall [serializerForType t, text "rab", srCall [getFieldAccessor f, "obj"],
              parens (text ("data_off + " ++ show offsetInBytes))]
    ) <+> lineComment (text "serialize field" <+> quotedStr (fieldName_ f) <+> pretty w <+> text "*" <+> pretty (byteSizeOfType t) <+> pretty t)

emitFieldSerializer f | (FieldGroup w) <- fieldUnion f =
  txCall [serializerForGroup w,
          text "rab", srCall [getFieldAccessor f, "obj"],
          text "nextoffset", text "data_off", text "ptrs_off"]
    <+> lineComment (text $ "serialize group '" ++ fieldName_ f ++ "'")

emitNodeUnionSerializer node@(NodeStruct {}) dname nodeid | nodeStruct_isGroup node == 0 = do
  let sizedata = nodeStruct_dataWordCount node
  let size     = nodeStruct_pointerCount node + sizedata
  let fnname   = serializerForType (Type_Struct nodeid)
  -- data fields first, then pointer fields
  return $
        fnDefinition (text $ "sr" ++ dname) [text "obj"] [text dname] (retTy "IO ByteString")
                     (txCall [text "serializeWith", text "obj", fnname])
    <$> fnDefinition fnname (splitArgs "obj rab ptr_off data_off")
                     (map text [dname, "ResizableArrayBuilder", "Word64", "Word64"]) (retTy "IO ()")
                     (doblock [text "let nextoffset = data_off +" <+> text (show (8 * size))
                              ,txCall (splitArgs $ helperForStructSerializer nodeid ++ " obj rab data_off nextoffset")
                              ,srCall ["sr_ptr_struct", "rab", "ptr_off", show sizedata, show (size - sizedata),
                                            show (txCall [text "delta_in_words", text "data_off",
                                                           emitAdd "ptr_off" "8"])]])
    <$> lineComment (text $ "Serialize the given object to data_off, with sub-objects serialized to nextoffset")
    <$> fnDefinition (text (helperForStructSerializer nodeid))
                     (splitArgs "obj rab data_off nextoffset") noArgTys noRetTy
                     (doblock [
                          text "let ptrs_off =" <+> emitAdd "data_off" (show (8 * sizedata))
                         ,if nodeStruct_discriminantCount node == 0
                            then vcat (map emitFieldSerializer (nodeStruct_fields node))
                            else
                                let indiscriminantFields = [f | f <- nodeStruct_fields node, fieldDiscriminant f == 0xffff] in
                                let discriminatedFields =  [f | f <- nodeStruct_fields node, fieldDiscriminant f /= 0xffff] in
                                text ("let absDiscrimOff = (data_off + (2 * " ++ show (nodeStruct_discriminantOffset node) ++ "))")
                            <$> match "obj" [(text (fieldCtorName f) <+> text "{}"
                                              ,doblock $ [srCall ["rabWriteWord16", "rab", "absDiscrimOff", show (fieldDiscriminant f)]
                                                        ,emitFieldSerializer f] ++
                                                        (map emitFieldSerializer indiscriminantFields))
                                                  | f <- discriminatedFields]
                       ])
    <$> fnDefinition (text ("sr_list_of_" ++ show nodeid))
                     (splitArgs "objs rab ptr_off data_off")
                     (splitArgs ("[" ++ dname ++ "] ResizableArrayBuilder Word64 Word64")) (retTy "IO ()")
         (doblock [
            case nodeStruct_preferredListEncoding node of
             7 ->
                       text ("let objsize = " ++ show (size * 8) ++ " :: Word64")
                   <$> text  "let num_elts = fromIntegral $ length objs"
                   <$> text  "let totalsize = objsize * num_elts"
                   <$> text  "let target_off = data_off + 8" <+> lineComment (text "accounting for tag word")
                   <$> srCall ["sr_composite_list_helper", "rab", "objsize", "target_off", 
                                 "(target_off + totalsize)", "objs", helperForStructSerializer nodeid]
                   <$> srCall ["sr_ptr_struct", "rab", "data_off", show sizedata, show (size - sizedata), "num_elts"]
                   <$> txCall [text "sr_ptr_list", text "rab", text "ptr_off", text "7",
                                  srCall ["div", "totalsize", "8"],
                                  srCall ["delta_in_words", "data_off", "(ptr_off + 8)"]]
             1 -> error $ "Can't yet support serialization of lists of single-bit structs."
             siz ->
                       --text ("let objsize = " ++ show ((byteSizeOfListEncoding siz) * 8) ++ " :: Word64")
                       text  "-- TODO test this..."
                   <$> text  "let objsize = " <> text (show (byteSizeOfListEncoding siz))
                   <$> text  "let num_elts = " <> srCall ["objsLength", "objs"]
                   <$> text  "let totalsize =" <+> txCall [text "sr_total_size_for", pretty (show siz), pretty (show $ size * 8), text "num_elts"]
                   <$> srCall ["sr_composite_list_helper", "rab", "objsize", "data_off", 
                                 "(data_off + totalsize)", "objs", helperForStructSerializer nodeid]
                   <$> txCall ((map text ["sr_ptr_list", "rab", "ptr_off", show siz, "num_elts"])
                                        ++ [srCall ["delta_in_words", "data_off", "(ptr_off + 8)"]])])

emitNodeUnionSerializer node@(NodeStruct {}) dname nodeid | nodeStruct_isGroup node /= 0 && nodeStruct_discriminantCount node == 0 = do
  let sizedata = nodeStruct_dataWordCount node
  let size    =  nodeStruct_pointerCount node + sizedata
  return $
    fnDefinition (serializerForGroup nodeid)
                 (map text ["rab", "obj", "nextoffset", "data_off", "ptrs_off"]) noArgTys noRetTy
              (doblock $ (text "let nextoffset = data_off +" <+> text (show (8 * size)))
                         :map emitFieldSerializer (nodeStruct_fields node))

emitNodeUnionSerializer node@(NodeStruct {}) dname nodeid | nodeStruct_isGroup node /= 0 && nodeStruct_discriminantCount node > 0 = do
  return $
    fnDefinition (serializerForGroup nodeid)
                 (map text ["rab", "obj", "nextoffset", "data_off", "ptrs_off"])
                 noArgTys noRetTy
                 (doblock [text $ "let absDiscrimOff = (data_off + (2 * " ++ show (nodeStruct_discriminantOffset node) ++ "))"
                          ,match "obj" [
                             (text (fieldCtorName f) <+> text "{}",
                              doblock [srCall ["rabWriteWord16", "rab", "absDiscrimOff", show (fieldDiscriminant f)]
                                      ,emitFieldSerializer f])
                             | f <- nodeStruct_fields node]])

emitNodeUnionSerializer node@(NodeEnum {}) dname nodeid = do
  let fnname = serializerForType (Type_Enum nodeid)
  return $ fnDefinition fnname (splitArgs "rab e offset")
                        [text "ResizableArrayBuilder", text dname, text "Word64"] (retTy "IO ()")
              (doblock [text "let value = " <>
                               match "e"
                                [ (text (capitalizeFirstLetter $ legalizeIdent $ enumerantName en)
                                  ,pretty (enumerantOrder en))
                                | en <- nodeEnum_enumerants node]
                       ,txCall (splitArgs "rabWriteWord16 rab offset value")])

emitNodeUnionSerializer node dname nodeid = do
  return $ multiLineComment $ string (show (dname, nodeid, node))
-----

noArgTys = []
noRetTy = empty
retTy str = text str

splitArgs args = map text $ split " " args

emitNodeBuilder node = emitNodeUnionBuilder (nodeUnion node) (nodeDisplayName node) (nodeId node)

emitNodeUnionBuilder node@(NodeStruct {}) dname nodeid | nodeStruct_discriminantCount node /= 0 = do
  let fnname = makerForType (Type_Struct nodeid)
  let indiscriminantFields = [f | f <- nodeStruct_fields node, fieldDiscriminant f == 0xffff]
  let discriminatedFields =  [f | f <- nodeStruct_fields node, fieldDiscriminant f /= 0xffff]
  fieldAccessors <- mapM (emitGroupFieldAccessor indiscriminantFields) discriminatedFields
  let discoffb = nodeStruct_discriminantOffset node * 2
  let args = [text "obj"]
  return $  fnDefinition (text $ "mk" ++ dname) args noArgTys noRetTy (txCall [fnname, text "obj"])
        <$> fnDefinition fnname [text "obj@(StructObj bs ptrs)"] [text "Object"] (retTy dname)
                         (match (show (srCall ["at", "bs16", show discoffb, "bs"]))
                            [(text (show d), fieldAccessor)
                            | (d, fieldAccessor) <- zip (map fieldDiscriminant discriminatedFields) fieldAccessors])

emitNodeUnionBuilder node@(NodeStruct {}) dname nodeid = do
  let fnname = makerForType (Type_Struct nodeid)
  fieldAccessors <- mapM emitFieldAccessor (nodeStruct_fields node)
  return $  fnDefinition (text $ "mk" ++ dname) [text "obj"] [text "Object"] (retTy dname)
                         (txCall [fnname, text "obj"])
        <$> fnDefinition fnname [text "obj@(StructObj bs ptrs)"] [text "Object"] (retTy dname)
                         (doblock [txCall (text dname:fieldAccessors)])

emitNodeUnionBuilder node@(NodeEnum {}) dname nodeid = do
  let fnname = makerForType (Type_Enum nodeid)
  return $ fnDefinition fnname [text "w"] [text "Word16"] (retTy dname)
                        (match "w"
                          [ (pretty (enumerantOrder en)
                            ,text (capitalizeFirstLetter $ legalizeIdent $ enumerantName en))
                          | en <- nodeEnum_enumerants node])

emitNodeUnionBuilder other dname _ = do
  let fnname = "mk" ++ dname
  return $  fnDefinition (text fnname) [text "obj"] [text "Object"] (retTy dname)
                         (srCall ["error", show "emitNodeUnionBuilder other...?"])

emitGroupFieldAccessor commonFields f = do
  accs <- mapM emitFieldAccessor (commonFields ++ [f])
  return $ txCall ((text (fieldCtorName f)) : accs)

emitFieldAccessor f | FieldSlot w t v <- fieldUnion f = do
  case kindOfType t of
    KindPtr -> do
      let offset = fromIntegral w
      return $ extractPtr t offset <+> multiLineComment (text (show t))

    KindData -> do
      let offset = fromIntegral w * byteSizeOfType t
      return $ extractData t offset <+> multiLineComment (text (show t))

emitFieldAccessor f | FieldGroup w <- fieldUnion f = do
  return $ txCall [makerForType (Type_Struct w), text "obj"]

extractData :: Type_ -> Int -> Doc
extractData t offset =
  let accessor = srCall ["at", accessorNameForType t, show offset, "bs"] in
  case t of
    Type_Bool   -> srCall [accessorNameForType t, show offset, "bs"]
    Type_Enum w -> txCall [makerForType t, accessor]
    _           -> accessor

extractPtrFunc :: Type_ -> Doc
extractPtrFunc t =
   case t of
     Type_Text        -> text "unStrObj"
     Type_Data        -> error "xPF Data"
     Type_List      x -> error $ "xPF List of " ++ show x
     Type_Struct    _ -> makerForType t
     Type_Interface _ -> error "xPF Interface"
     Type_Object      -> error "xPF Object"
     Type_Void        -> text "mk_void"
     _ -> error $ "extractPtrFunc saw unexpected type " ++ show t

extractPtr :: Type_ -> Int -> Doc
extractPtr t offset =
  let ptr = emitListIndex "ptrs" offset in
  parens $
    case t of
     Type_Text        -> extractPtrFunc t <+> ptr
     Type_Data        -> text "<unsupported extractPtr type:" <+> text (show t)
     Type_List      x -> text "mapL \"xP\"" <+> extractPtrFunc x <+> ptr
     Type_Struct    _ -> extractPtrFunc t <+> ptr
     Type_Interface _ -> text "<unsupported extractPtr type:" <+> text (show t)
     Type_Object      -> text "<unsupported extractPtr type:" <+> text (show t)
     _ -> error $ "extractPtr saw unexpected type " ++ show t

spanList _ [] = ([],[])
spanList func list@(x:xs) =
    if func list
       then (x:ys,zs)
       else ([],list)
    where (ys,zs) = spanList func xs

breakList :: ([a] -> Bool) -> [a] -> ([a], [a])
breakList func = spanList (not . func)

split :: Eq a => [a] -> [a] -> [[a]]
split _ [] = []
split delim str =
    let (firstline, remainder) = breakList (isPrefixOf delim) str
        in
        firstline : case remainder of
                                   [] -> []
                                   x -> if x == delim
                                        then [] : []
                                        else split delim
                                                 (drop (length delim) x)
sjoin delim s = concat (intersperse delim s)
replace old new s = sjoin new . split old $ s
legalizeTypeName fs = case split ":" fs of
                        [_, s] -> replace "." "_" s
                        [s]    -> replace "." "_" s

denoteNodeAttributes node = do
  denoteNodeId node
  case nodeUnion node of
     ns@(NodeStruct {}) -> do
       denoteStructEncodingTag (nodeId node)
                               (nodeStruct_preferredListEncoding ns)
     _ -> return ()

denoteNodeId node = do
  denoteId (nodeId node) (nodeDisplayName node)

instance CGHS Node where
  cgHS node = do
    arms <- computeDataArms (nodeDisplayName node) (nodeUnion node)
    return $ formatDataDecl (nodeDisplayName node) (nodeId node) arms
          <$> multiLineComment (string (show node))

computeDataArms :: String -> NodeUnion -> CG [(Doc, [Doc])]
computeDataArms _  NodeFile = return []
computeDataArms _  (NodeConst t v) = error $ "computeDataArms NodeConst"
computeDataArms _  (NodeInterface _) = error $ "computeDataArms NodeInterface"
computeDataArms _  (NodeEnum enums) = return $ map armCaseOfEnum enums
computeDataArms _  na@(NodeAnnotation {}) = do return []
computeDataArms nm ns@(NodeStruct {}) = do
    if nodeStruct_discriminantCount ns /= 0
      then do
        let indiscriminantFields =    [f | f <- nodeStruct_fields ns, fieldDiscriminant f == 0xffff]
        arms <- mapM caseArmOfFieldGG [f | f <- nodeStruct_fields ns, fieldDiscriminant f /= 0xffff]
        prependFields indiscriminantFields arms
      else do
        fields <- mapM caseArmOfFieldNG (nodeStruct_fields ns)
        return [(text nm, fields)]

prependFields fields arms = do
  let doPrependFields (ctor, params) = do
         fieldparams <- mapM caseArmOfFieldNG fields
         return (ctor, fieldparams ++ params)
  mapM doPrependFields arms

armCaseOfEnum :: Enumerant -> (Doc, [Doc])
armCaseOfEnum e = (armNameOfEnum e, [])

armNameOfEnum e = text (capitalizeFirstLetter $ legalizeIdent $ enumerantName e)

caseArmOfFieldGG f = do
    ty <- cgHS (fieldUnion f)
    return $ (text (fieldCtorName f), [text (fieldUnCtorName f) <+> text "::" <+> ty])

caseArmOfFieldNG f = do
    ty <- cgHS $ fieldUnion f
    return $ (text (fieldName f) <+> text "::" <+> ty)

-- Example: for a field "foo", fieldCtorName would be "Foo" and fieldUnCtorName would be "unFoo"
fieldCtorName f = capitalizeFirstLetter $ fieldName f
fieldUnCtorName f = "un" ++ fieldCtorName f

capitalizeFirstLetter [] = []
capitalizeFirstLetter (h:t) = toUpper h : t

legalizeIdent "type" = "type_"
legalizeIdent "id"   = "id_"
legalizeIdent str = str

instance CGHS FieldUnion where
  cgHS (FieldSlot _ t _) = do cgHS t
  cgHS (FieldGroup w) = do liftM text (lookupId w)

instance CGHS Type_ where
  cgHS type_ =
    case type_ of
      Type_Void        -> return $ text "()"
      Type_Bool        -> return $ text "Bool"
      Type_Int8        -> return $ text "Int8"
      Type_Int16       -> return $ text "Int16"
      Type_Int32       -> return $ text "Int32"
      Type_Int64       -> return $ text "Int64"
      Type_UInt8       -> return $ text "Word8"
      Type_UInt16      -> return $ text "Word16"
      Type_UInt32      -> return $ text "Word32"
      Type_UInt64      -> return $ text "Word64"
      Type_Float32     -> return $ text "Float"
      Type_Float64     -> return $ text "Double"
      Type_Text        -> return $ text "String"
      Type_Data        -> return $ text "ByteString"
      Type_List      t -> do tx <- cgHS t
                             return $ text "[" <> tx <> text "]"
      Type_Enum      w -> liftM text (lookupId w)
      Type_Struct    w -> liftM text (lookupId w)
      Type_Interface w -> liftM text (lookupId w)
      Type_Object      -> return $ text "<...object...>"

formatDataDecl name nodeid arms =
      lineComment (pretty nodeid)
  <$> text "data" <+> text name <+> text "="
        <$> indent 4 (cases (map formatDataArm arms)
                      <$> text "deriving Show")
        <$> text ""

formatDataArm (armName, []) = armName

formatDataArm (armName, armFields) =
  armName <+> text "{"
    <$> indent 4 (embedded armFields)
    <$> text "}"

cases :: [Doc] -> Doc
cases []         = text ""
cases [doc]      = doc
cases (doc:docs) = vsep $ (text " " <+> doc) : (map (\d -> text "|" <+> d) docs)

embedded :: [Doc] -> Doc
embedded docs = vsep $ map (\(d,p) -> text p <+> d) (zip docs (" ":repeat ","))

denoteId :: Word64 -> String -> CG ()
denoteId w s = do
  (CG_State m1 m2) <- get
  put $ CG_State (Map.insert w s m1) m2

lookupId :: Word64 -> CG String
lookupId w = do
  (CG_State m _) <- get
  return $ case Map.lookup w m of
              Nothing -> "<unknown!>"
              Just s  -> s

denoteStructEncodingTag :: Word64 -> Word16 -> CG ()
denoteStructEncodingTag w v = do
  CG_State m1 m2 <- get
  put $ CG_State m1 (Map.insert w v m2)

------------------------------------------------------------
-- For a NodeStruct, we get a pointer to the serialized struct
-- from absoffset, dataWordCount and pointerCount, where absoffset
-- is an absolute offset for the start of the serialized content.
-- The actual pointer offset is the relative distance from the
-- location of the serialized pointer to the absoffset.
--
-- For each unboxed field of a struct, we write the value to the
-- given offset; for pointers, we serialize the pointed-to value,
-- yielding a pointer, which we store. Pointers to group objects
-- should be serialized into the parent object rather than newly
-- allocated space.
--
lookupListEltSizeTag :: Word64 -> CG Word16
lookupListEltSizeTag w = do
  (CG_State _ m) <- get
  return $ case Map.lookup w m of
              Nothing -> error $ "Unknown list elt size for " ++ show w
              Just v  -> v

listEltSizeTag t = case t of
     Type_Void        -> return 0
     Type_Bool        -> return 1
     Type_Int8        -> return 2
     Type_Int16       -> return 3
     Type_Int32       -> return 4
     Type_Int64       -> return 5
     Type_UInt8       -> return 2
     Type_UInt16      -> return 3
     Type_UInt32      -> return 4
     Type_UInt64      -> return 5
     Type_Float32     -> return 4
     Type_Float64     -> return 5
     Type_Text        -> return 6
     Type_Data        -> return 6
     Type_List      _ -> return 6
     Type_Enum      _ -> return 3 -- or composite?
     Type_Struct    w -> lookupListEltSizeTag w
     Type_Interface _ -> error $ "listEltSizeTag Interface"
     Type_Object      -> error $ "listEltSizeTag AnyPointer"
------------------------------------------------------------

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

nodeDisplayName n = legalizeTypeName $ nodeDisplayName_ n

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
    , fieldUnion   :: FieldUnion
    , fieldOrdinal :: FieldOrdinal
} deriving Show

fieldName f = legalizeIdent $ fieldName_ f

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
   | Value_Object   Object
   | Value_ERROR
   deriving Show

data Kind = KindData | KindPtr deriving (Eq, Show)

kindOfType t = case t of
     Type_Void        -> KindData
     Type_Bool        -> KindData
     Type_Int8        -> KindData
     Type_Int16       -> KindData
     Type_Int32       -> KindData
     Type_Int64       -> KindData
     Type_UInt8       -> KindData
     Type_UInt16      -> KindData
     Type_UInt32      -> KindData
     Type_UInt64      -> KindData
     Type_Float32     -> KindData
     Type_Float64     -> KindData
     Type_Text        -> KindPtr
     Type_Data        -> KindPtr
     Type_List      _ -> KindPtr
     Type_Enum      _ -> KindData
     Type_Struct    _ -> KindPtr
     Type_Interface _ -> KindPtr
     Type_Object      -> KindPtr

--------------------------------------------------------------------

mkCodeGeneratorRequest :: Object -> CodeGeneratorRequest
mkCodeGeneratorRequest (StructObj _bs [nodes, reqfiles]) =
  CodeGeneratorRequest (mapL "cgr" mkNode nodes) (mapL "mkcg" mkRequestedFile reqfiles)

mkRequestedFile (StructObj bs [name, _imports]) = RequestedFile id (unStrObj name)
  where id = at bs64 0 bs
mkRequestedFile other = error $ "mkRequestedFile " ++ show (pretty other)

mkNode          (StructObj bs
                           (displayNameStrObj:
                            nestedNodes:
                            annotations:rest)) =
    Node id scopeId prefixLen (unStrObj displayNameStrObj) union (mapL "NestedNodes" mkNestedNode nestedNodes)
      where
          id        = at bs64  0 bs
          prefixLen = at bs32  8 bs
          which     = at bs16 12 bs
          scopeId   = at bs64 16 bs
          union     = case which of
                        0 -> NodeFile
                        1 -> NodeStruct (at bs16 14 bs)
                                        (at bs16 24 bs)
                                        (at bs16 26 bs)
                                        (at bs8  28 bs)
                                        (at bs16 30 bs)
                                        (at bs16 32 bs)
                                        (mapL "NodeFields" mkField (rest !! 0))
                        2 -> NodeEnum (mapL "NodeE" mkEnumerant (rest !! 0))
                        3 -> NodeInterface (mapL "NodeI" mkMethod (rest !! 0))
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
  Field (unStrObj name) codeOrder discriminantValue t1 explicit
    where codeOrder = at bs16 0 bs
          discriminantValue = (at bs16 2 bs) `xor` (65535 :: Word16)
          which = at bs16 8 bs
          t1 = case which of
                0 -> FieldSlot (at bs32 4 bs)
                               (mkType  $ rest !! 0)
                               (mkValue $ rest !! 1)
                1 -> FieldGroup (at bs64 16 bs)
                _ -> error "Field which1"
          explicit = case at bs16 10 bs of
                       0 -> FieldOrdinalImplicit
                       1 -> FieldOrdinalExplicit (at bs16 12 bs)

--mkField other = Field "<erroneous field>" 0 0 (FieldGroup 0) FieldOrdinalImplicit
mkField other = error $ "mkField couldn't handle\n" ++ show (pretty other)

mkType :: Object -> Type_
mkType (StructObj bs objs) =
  let which = at bs16 0 bs in
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
    15 -> Type_Enum       (at bs64 8 bs)
    16 -> Type_Struct     (at bs64 8 bs)
    17 -> Type_Interface  (at bs64 8 bs)
    18 -> Type_Object

mkValue :: Object -> Value
mkValue (StructObj bs objs) =
  let which = at bs16 0 bs in
  case which of
    0  -> Value_Void
    1  -> Value_Bool     (at bs8  2 bs `mod` 2 == 1)
    2  -> Value_Int8     (at bs8  2 bs)
    3  -> Value_Int16    (at bs16 2 bs)
    4  -> Value_Int32    (at bs32 2 bs)
    5  -> Value_Int64    (at bs64 2 bs)
    6  -> Value_UInt8    (at bs8  2 bs)
    7  -> Value_UInt16   (at bs16 2 bs)
    8  -> Value_UInt32   (at bs32 2 bs)
    9  -> Value_UInt64   (at bs64 2 bs)
    10 -> Value_Float32  (wordToFloat  $ at bs32 2 bs)
    11 -> Value_Float64  (wordToDouble $ at bs64 2 bs)
    12 -> Value_Text     (unStrObj $ objs !! 0)
    13 -> Value_Data     (unStrObj $ objs !! 0)
    14 -> Value_List       
    15 -> Value_Enum     (at bs16 2 bs)
    16 -> Value_Struct     
    17 -> Value_Interface  
    18 -> Value_Object   (objs !! 0)
    _  -> Value_ERROR

mkMethod (StructObj bs (name:rest)) =
  Method (unStrObj name) (at bs16 0 bs)

mkNestedNode (StructObj bs [name]) = NestedNode (unStrObj name) (at bs64 0 bs)

mkEnumerant (StructObj bs (name:rest)) =
  Enumerant (unStrObj name) (at bs16 0 bs)

--------------------------------------------------------------------

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

byteSizeOfListEncoding n =
  case n of
    2 -> 1
    3 -> 2
    4 -> 4
    5 -> 8
    6 -> 8
    _ -> error $ "byteSizeOfListEncoding requires n to be [2..6]; had " ++ show n
