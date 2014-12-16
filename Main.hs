{-# LANGUAGE ImplicitParams #-}
module Main where

import Minuproto
import MinuprotoBootstrap
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

import Debug.Trace(trace)

import Data.Map(Map)
import qualified Data.Map as Map

import Data.List(intersperse, isPrefixOf)

import Control.Monad.State
import System.IO(withFile, stdin, IOMode(WriteMode))

main = do
  rawbytes <- BS.hGetContents stdin
  let segments@(seg:_) = splitSegments rawbytes
  let obj = parseSegment seg segments
  putStrLn $ "had this many segments: " ++ show (length segments)
  let cgr = mkCodeGeneratorRequest obj
  let hs_code_doc = evalState (cgCodeGeneratorRequest cgr)
                              (CG_State Map.empty Map.empty)
  --putStrLn $ "obj is:"
  --putDoc $ pretty obj <> line
  --putDoc $ hs_code_doc
  let ?tgt = targetHaskell
  modularizeAndPutDocToFile hs_code_doc (rfName ((cgrRequestedFiles cgr) !! 0))

------------------------------------------------------------
moduleNameOf str = capitalizeFirstLetter $ replaceWith '.' '_' str
replaceWith c r str = map (\v -> if v == c then r else v) str
------------------------------------------------------------
modularizeAndPutDocToFile :: (?tgt::TargetLanguage) => Doc -> String -> IO ()
modularizeAndPutDocToFile d protoname =
  putDocToFile (targetHeader protoname <$> d)
               (targetFilename protoname)
------------------------------------------------------------
putDocToFile d f = do
  putStrLn $ "writing to output file " ++ f
  withFile f WriteMode (\h -> hPutDoc h d)
------------------------------------------------------------

targetHeader :: (?tgt::TargetLanguage) => String -> Doc
targetHeader   = _targetHeader   ?tgt

targetFilename :: (?tgt::TargetLanguage) => String -> String
targetFilename = _targetFilename ?tgt

targetCall :: (?tgt::TargetLanguage) => [Doc] -> Doc
targetCall   = _targetCall ?tgt

data TargetLanguage = TargetLanguage {
    _targetHeader   :: String -> Doc
  , _targetFilename :: String -> String
  , _targetCall     :: [Doc]  -> Doc
}

targetHaskell = TargetLanguage
                  hsTargetHeader
                  hsTargetFilename
                  hsTargetCall
  where
    hsTargetFilename protoname = moduleNameOf protoname ++ ".hs"
    hsTargetHeader   protoname = vcat $
                          [ text "{-# LANGUAGE BangPatterns #-}"
                          , text "module" <+> text (moduleNameOf protoname) <+> text "where"
                          , text "import Data.ByteString(ByteString)"
                          , text "import Minuproto"
                          , text "import ResizableArrayBuilder"
                          , text "import Data.Word"
                          , text "import Data.Int"
                          ]
    hsTargetCall (doc:docs) = parens $ doc <+> align (vsep docs)

data CG_State =
     CG_State (Map Word64 String)
              (Map Word64 Word16)

type CG t = State CG_State t

cgCodeGeneratorRequest :: CodeGeneratorRequest -> CG Doc
cgCodeGeneratorRequest cgr = do
    -- Build the mapping of node ids to type names for later pretty-printing.
    mapM_ denoteNodeAttributes (cgrNodes cgr)
    -- Emit the data type declaration for each node.
    let productiveNodes = filter isNodeProductive (cgrNodes cgr)
    ns <- mapM cgNode productiveNodes
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

serializerForType (Type_Enum   w) = text $ "sr_enum_"   ++ show w
serializerForType (Type_Struct w) = text $ "sr_struct_" ++ show w
serializerForType (Type_List (Type_Struct w)) = text $ "sr_list_of_" ++ show w
serializerForType (Type_List (Type_Enum   w)) = text $ "sr_list_of_" ++ show w
serializerForType (Type_List t) = text $ "sr_list_of_" ++ show t
serializerForType t = text ("sr_" ++ show t)

nodeDisplayName n = legalizeTypeName $ nodeDisplayName_ n

srCall strs = parens (foldl1 (<+>) (map text strs))
txCall strs = parens (foldl1 (<+>) (         strs))
pair a b = parens (a <> text ", " <> b)
quoted d = squote <> d <> squote
quotedStr s = quoted (text s)

instance Pretty Word32 where pretty w = pretty (show w)
instance Pretty Type_  where pretty w = pretty (show w)

getFieldAccessor typename f =
  if fieldDiscriminant f /= 0xffff
    then fieldUnCtorName typename f
    else fieldName       typename f

serializerForFieldType f t =
  if isFieldOptional f
    then txCall [text "sr_Maybe", serializerForType t]
    else serializerForType t

emitFieldSerializer typename f | (FieldSlot offsetInBits Type_Bool _) <- fieldUnion f =
  (txCall [serializerForFieldType f Type_Bool, text "rab", srCall [getFieldAccessor typename f, "obj"],
           text "data_off", pretty offsetInBits])
     <+> lineComment (text "serialize bool field" <+> quotedStr (fieldName_ f))

emitFieldSerializer typename f | (FieldSlot w t _) <- fieldUnion f =
  let offsetInBytes = fromIntegral w * byteSizeOfType t in
  (case kindOfType t of
    KindPtr ->
      txCall [serializerForFieldType f t, srCall [getFieldAccessor typename f, "obj"], text "rab", parens (text "ptrs_off +" <+> text (show offsetInBytes)), text "nextoffset"]
      <$> text "nextoffset <- updateNextOffset rab nextoffset ; return ()"
    KindData ->
      txCall [serializerForFieldType f t, text "rab", srCall [getFieldAccessor typename f, "obj"],
              parens (text ("data_off + " ++ show offsetInBytes))]
    ) <+> lineComment (text "serialize field" <+> quotedStr (fieldName_ f) <+> pretty w <+> text "*" <+> pretty (byteSizeOfType t) <+> pretty t)

emitFieldSerializer typename f | (FieldGroup w) <- fieldUnion f =
  txCall [text ("sr_group_" ++ (show w)), text "rab", srCall [getFieldAccessor typename f, "obj"], text "nextoffset", text "data_off", text "ptrs_off"]
    <+> lineComment (text $ "serialize group '" ++ fieldName_ f ++ "'")

emitNodeUnionSerializer node@(NodeStruct {}) dname nodeid | nodeStruct_isGroup node == 0 = do
  let sizedata = nodeStruct_dataWordCount node
  let size    =  nodeStruct_pointerCount node + sizedata
  -- data fields first, then pointer fields
  return $
        text ("sr" ++ dname ++ " :: " ++ dname ++ " -> IO ByteString")
    <$> text ("sr" ++ dname ++ " !obj = serializeWith obj sr_struct_" ++ show nodeid)
    <$> text ""
    <$> text ("sr_struct_" ++ show nodeid ++ " :: " ++ dname ++ " -> ResizableArrayBuilder -> Word64 -> Word64 -> IO ()")
    <$> text ("sr_struct_" ++ show nodeid ++ " !obj !rab !ptr_off !data_off = do")
    <$> indent 4 (
                       text "let !nextoffset = data_off +" <+> text (show (8 * size))
                   <$> text ("sr_struct_helper_" ++ show nodeid ++ " obj rab data_off nextoffset")
                   <$> srCall ["sr_ptr_struct rab ptr_off", show sizedata, show (size - sizedata),
                                                         "(delta_in_words data_off (ptr_off + 8))"]
                 )
    <$> text ""
    <$> lineComment (text $ "Serialize the given object to data_off, with sub-objects serialized to nextoffset")
    <$> text ("sr_struct_helper_" ++ show nodeid ++ " !obj !rab !data_off !nextoffset = do")
    <$> indent 4 (     text "let !ptrs_off = data_off +" <+> text (show (8 * sizedata))
                   <$> if nodeStruct_discriminantCount node == 0
                        then vsep (map (emitFieldSerializer dname) (nodeStruct_fields node))
                        else 
                             let indiscriminantFields = [f | f <- nodeStruct_fields node, fieldDiscriminant f == 0xffff] in
                             let discriminatedFields =  [f | f <- nodeStruct_fields node, fieldDiscriminant f /= 0xffff] in
                             text ("let !absDiscrimOff = (data_off + (2 * " ++ show (nodeStruct_discriminantOffset node) ++ "))")
                         <$> text "case obj of"
                         <$> indent 4 (vsep [text (fieldCtorName dname f) <+> text "{}" <+> text "->"
                                                <+> (text "do" <$> indent 2 (vsep [srCall ["rabWriteWord16", "rab", "absDiscrimOff", show (fieldDiscriminant f)]
                                                                                  ,emitFieldSerializer dname f])
                                                               <$> indent 2 (vsep (map (emitFieldSerializer dname) indiscriminantFields)))
                                              | f <- discriminatedFields])
                )
    <$> text ""
    <$> text ("sr_list_of_" ++ show nodeid ++ " :: [" ++ dname ++ "] -> ResizableArrayBuilder -> Word64 -> Word64 -> IO ()")
    <$> text ("sr_list_of_" ++ show nodeid ++ " !objs !rab !ptr_off !data_off = do")
    <$> indent 4 (
           case nodeStruct_preferredListEncoding node of
             7 ->
                       text ("let !objsize = " ++ show (size * 8) ++ " :: Word64")
                   <$> text  "let !num_elts = fromIntegral $ length objs"
                   <$> text  "let !totalsize = objsize * num_elts"
                   <$> text  "let !target_off = data_off + 8" <+> lineComment (text "accounting for tag word")
                   <$> text ("sr_composite_list_helper rab objsize target_off (target_off + totalsize) objs sr_struct_helper_" ++ show nodeid ++ "")
                   <$> srCall ["sr_ptr_struct", "rab", "data_off", show sizedata, show (size - sizedata), "num_elts"]
                   <$> text "sr_ptr_list rab ptr_off 7 (totalsize `div` 8) (delta_in_words data_off (ptr_off + 8))"
             1 -> error $ "Can't yet support serialization of lists of single-bit structs."
             siz ->
                       --text ("let objsize = " ++ show ((byteSizeOfListEncoding siz) * 8) ++ " :: Word64")
                       text  "-- TODO test this..."
                   <$> text  "let !objsize = " <> text (show (byteSizeOfListEncoding siz))
                   <$> text  "let !num_elts = fromIntegral $ length objs"
                   <$> text  "let !totalsize =" <+> txCall [text "sr_total_size_for", pretty (show siz), pretty (show $ size * 8), text "num_elts"]
                   <$> text ("sr_composite_list_helper rab objsize data_off (data_off + totalsize) objs sr_struct_helper_" ++ show nodeid ++ "")
                   <$> text "sr_ptr_list rab ptr_off " <> pretty (show siz) <> text " num_elts (delta_in_words data_off (ptr_off + 8))"
                  )
    <$> text ""

emitNodeUnionSerializer node@(NodeStruct {}) dname nodeid | nodeStruct_isGroup node /= 0 && nodeStruct_discriminantCount node == 0 = do
  let sizedata = nodeStruct_dataWordCount node
  let size    =  nodeStruct_pointerCount node + sizedata
  return $ text ""
    <$> text ("sr_group_" ++ show nodeid ++ " !rab !obj !nextoffset !data_off !ptrs_off = do")
    <$> indent 4 (
                       text "let !nextoffset = data_off +" <+> text (show (8 * size))
                   <$> vsep (map (emitFieldSerializer dname) (nodeStruct_fields node))
                 )
    <$> text ""

emitNodeUnionSerializer node@(NodeStruct {}) dname nodeid | nodeStruct_isGroup node /= 0 && nodeStruct_discriminantCount node > 0 = do
  return $ text ""
    <$> text ("sr_group_" ++ show nodeid ++ " rab obj nextoffset data_off ptrs_off = do")
    <$> indent 4 (text $ "let !absDiscrimOff = (data_off + (2 * " ++ show (nodeStruct_discriminantOffset node) ++ "))")
    <$> indent 4 (text "case obj of")
    <$> indent 6 (vsep [text (fieldCtorName dname f) <+> text "{}" <+> text "->"
                          <+> (text "do" <$> indent 2 (vsep [srCall ["rabWriteWord16", "rab", "absDiscrimOff", show (fieldDiscriminant f)]
                                                            ,emitFieldSerializer dname f]))
                        | f <- nodeStruct_fields node])
    <$> text ""

emitNodeUnionSerializer node@(NodeEnum {}) dname nodeid = do
  let fnname = "sr_enum_" ++ show nodeid
  return $ text (fnname ++ " :: ResizableArrayBuilder -> " ++ dname ++ " -> Word64 -> IO ()")
        <$> text fnname <+> text "!rab !e !offset" <+> text "= do"
        <$> indent 2 (text "let !value =" <+> (indent 0 $ (text "case e of")
            <$> indent 2 (vsep [text (capitalizeFirstLetter $ legalizeIdent $ enumerantName en)
                                              <+> text "->" <+> text (show (enumerantOrder en))
                              | en <- nodeEnum_enumerants node])))
        <$> indent 2 (text "rabWriteWord16 rab offset value")
        <$> text ""

emitNodeUnionSerializer node dname nodeid = do
  return $ vsep [text "{-", string (show (dname, nodeid, node)), text "-}"]
-----

emitNodeBuilder node = emitNodeUnionBuilder (nodeUnion node) (nodeDisplayName node) (nodeId node)

emitNodeUnionBuilder node@(NodeStruct {}) dname nodeid | nodeStruct_discriminantCount node /= 0 = do
  let fnname = "mk_struct_" ++ show nodeid
  let indiscriminantFields = [f | f <- nodeStruct_fields node, fieldDiscriminant f == 0xffff]
  let discriminatedFields =  [f | f <- nodeStruct_fields node, fieldDiscriminant f /= 0xffff]
  fieldAccessors <- mapM (emitGroupFieldAccessor dname indiscriminantFields) discriminatedFields
  let discoffb = nodeStruct_discriminantOffset node * 2
  return $  text ("mk" ++ dname ++ " obj = " ++ fnname ++ " obj")
        <$> text fnname <+> text "::" <+> text "Object -> " <> text dname
        <$> text fnname <+> text "obj | isDefaultObj obj = error $ " <> text (show $ "Unset value in non-optional field of type " ++ show dname)
        <$> text fnname <+> text "obj@(StructObj bs ptrs)" <+> text " = do "
        <$> indent 4 (text ("case (at bs16 " ++ show discoffb ++ " bs) of"))
        <$> indent 8 (vsep [text (show d) <+> text "->" <+> fieldAccessor | (d, fieldAccessor) <- zip (map fieldDiscriminant discriminatedFields) fieldAccessors])
        <$> text ""

emitNodeUnionBuilder node@(NodeStruct {}) dname nodeid = do
  let fnname = "mk_struct_" ++ show nodeid
  fieldAccessors <- mapM emitFieldAccessor (nodeStruct_fields node)
  return $  text ("mk" ++ dname ++ " obj = " ++ fnname ++ " obj")
        <$> text fnname <+> text "::" <+> text "Object -> " <> text dname
        <$> text fnname <+> text "obj | isDefaultObj obj = error $ " <> text (show $ "Unset value in non-optional field of type " ++ show dname)
        <$> text fnname <+> text "obj@(StructObj bs ptrs)" <+> text " = do "
        <$> indent 4 (parens (text dname
                               <+> indent 0 (vsep fieldAccessors)))
        <$> text ""

emitNodeUnionBuilder node@(NodeEnum {}) dname nodeid = do
  let fnname = "mk_enum_" ++ show nodeid
  return $  text fnname <+> text "::" <+> text "Word16 -> " <> text dname
        <$> text fnname <+> text "w" <+> text "="
        <$> indent 2 (text "case w of")
        <$> indent 4 (vsep [text (show (enumerantOrder en)) <+> text "->" <+> text (capitalizeFirstLetter $ legalizeIdent $ enumerantName en)
                           | en <- nodeEnum_enumerants node])
        <$> text ""

emitNodeUnionBuilder other dname _ = do
  let fnname = "mk" ++ dname
  return $  text fnname <+> text "::" <+> text "Object -> " <> text dname
        <$> text fnname <+> text "obj" <+> text " = "
        <$> indent 4 (parens (text dname
                               <+> hsep []))
        <$> text ""

emitGroupFieldAccessor typename commonFields f = do
  accs <- mapM emitFieldAccessor (commonFields ++ [f])
  return $ txCall ((text (fieldCtorName typename f)) : accs)

emitFieldAccessor f | FieldSlot w t v <- fieldUnion f = do
  case kindOfType t of
    KindPtr -> do
      let offset = fromIntegral w
      return $ extractPtr f (show t) t offset <+> text "{-" <+> text (show t) <+> text "-}"

    KindData -> do
      let offset = fromIntegral w * byteSizeOfType t
      return $ extractData t offset <+> text "{-" <+> text (show t) <+> text "-}"

emitFieldAccessor f | FieldGroup w <- fieldUnion f = do
  return $ parens $ text $ "mk_struct_" ++ show w ++ " obj"

extractData :: Type_ -> Int -> Doc
extractData t offset =
  let accessor = srCall ["at", accessorNameForType t, show offset, "bs"] in
  case t of
    Type_Bool   -> srCall [accessorNameForType t, show offset, "bs"]
    Type_Enum w -> parens $ text ("mk_enum_" ++ show w) <+> accessor
    _           -> accessor

extractPtrFunc :: Field -> Type_ -> Doc
extractPtrFunc f t =
   let wrapper d = if isFieldOptional f
                     then text "_mkMaybe" <+> d
                     else                     d
   in wrapper $ case t of
     Type_Text        -> text "unStrObj"
     Type_Data        -> text "unBytes"
     Type_List      x -> error $ "xPF List of " ++ show x
     Type_Struct    w -> text "mk_struct_" <> text (show w)
     Type_Interface _ -> error "xPF Interface"
     Type_Object      -> error "xPF Object"
     Type_Void        -> text "mk_void"
     Type_Bool        -> text "mk_Bool"
     Type_UInt64      -> text "mk_Word64"
     _ -> error $ "extractPtrFunc saw unexpected type " ++ show t

extractPtr :: Field -> String -> Type_ -> Int -> Doc
extractPtr f msg t offset =
  let ptr = srCall ["lookupPointer", show msg, "ptrs", show offset] in
  parens $
    case t of
     Type_Text        -> extractPtrFunc f t <+> ptr
     Type_Data        -> extractPtrFunc f t <+> ptr
     Type_List      x -> text ("mapL \"" ++ show x ++ "\"") <+> extractPtrFunc f x <+> ptr
     Type_Struct    _ -> extractPtrFunc f t <+> ptr
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

cgNode :: Node -> CG Doc
cgNode node = do
    arms <- computeDataArms (nodeDisplayName node) (nodeUnion node)
    return $ formatDataDecl (nodeDisplayName node) (nodeId node) arms <$> text "{-" <$> string (show node) <$> text "-}"

lineComment doc = text "--" <+> doc

computeDataArms :: String -> NodeUnion -> CG [(Doc, [Doc])]
computeDataArms _  NodeFile = return []
computeDataArms _  (NodeConst t v) = error $ "computeDataArms NodeConst"
computeDataArms _  (NodeInterface _) = error $ "computeDataArms NodeInterface"
computeDataArms _  (NodeEnum enums) = return $ map armCaseOfEnum enums
computeDataArms _  na@(NodeAnnotation {}) = do return []
computeDataArms nm ns@(NodeStruct {}) = do
    if nodeStruct_discriminantCount ns /= 0
      then do
        let indiscriminantFields =         [f | f <- nodeStruct_fields ns, fieldDiscriminant f == 0xffff]
        arms <- mapM (caseArmOfFieldGG nm) [f | f <- nodeStruct_fields ns, fieldDiscriminant f /= 0xffff]
        prependFields nm indiscriminantFields arms
      else do
        fields <- mapM (caseArmOfFieldNG nm) (nodeStruct_fields ns)
        return [(text nm, fields)]

prependFields typename fields arms = do
  let doPrependFields (ctor, params) = do
         fieldparams <- mapM (caseArmOfFieldNG typename) fields
         return (ctor, fieldparams ++ params)
  mapM doPrependFields arms

armCaseOfEnum :: Enumerant -> (Doc, [Doc])
armCaseOfEnum e = (armNameOfEnum e, [])

armNameOfEnum e = text (capitalizeFirstLetter $ legalizeIdent $ enumerantName e)

caseArmOfFieldGG typename f = do
    ty <- cgFieldUnion f (fieldUnion f)
    return $ (text (fieldCtorName typename f)
             ,[text (fieldUnCtorName typename f) <+> text "::" <+> strictField ty])

caseArmOfFieldNG typename f = do
    ty <- cgFieldUnion f (fieldUnion f)
    return $ (text (fieldName typename f) <+> text "::" <+> strictField ty)

strictField doc = text "!" <> doc

-- Example: for a field "foo" of type Ty, fieldCtorName would be "Ty_foo" and fieldUnCtorName would be "unTy_foo"
fieldCtorName   typename f = capitalizeFirstLetter $ fieldName typename f
fieldUnCtorName typename f = "un" ++ fieldCtorName typename f

capitalizeFirstLetter [] = []
capitalizeFirstLetter (h:t) = toUpper h : t

legalizeIdent "type" = "type_"
legalizeIdent "id"   = "id_"
legalizeIdent str = str

cgFieldUnion f (FieldGroup w)    = do liftM text (lookupId w)
cgFieldUnion f (FieldSlot _ t _) = do ty <- cgFieldSlotType t
                                      if isFieldOptional f
                                        then return $ parens $ text "StrictMaybe" <+> ty
                                        else return ty
cgFieldSlotType type_ =
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
      Type_List      t -> do tx <- cgFieldSlotType t
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

