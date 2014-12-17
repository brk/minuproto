{-# LANGUAGE ImplicitParams #-}
-- vim: set foldmethod=marker
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
import System.IO(withFile, IOMode(WriteMode), stdin, stdout)

main = do
  rawbytes <- BS.hGetContents stdin
  let segments@(seg:_) = splitSegments rawbytes
  let obj = parseSegment seg segments
  let cgr = mkCodeGeneratorRequest obj
  let ?tgt = targetHaskell
  let hs_code_doc = evalState (cgCodeGeneratorRequest cgr)
                              (CG_State Map.empty Map.empty)
  --putStrLn $ "obj is:"
  --putDoc $ pretty obj <> line
  --putDoc $ hs_code_doc
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
hPutDocWide h d = displayIO h (renderPretty 0.9 110 d)

putDocToFile d f = do
  putStrLn $ "writing to output file " ++ f
  withFile f WriteMode (\h -> hPutDocWide h d)
------------------------------------------------------------

-- {{{ Explicit dictionary-passing, encoded using a
--     dynamically-scoped/implicit record parameter.
--
-- I think (?) that later versions of GHC could be convinced
-- to generate the appropriate dictionary-passing code
-- by using NullaryTypeClasses and OverlappingInstances,
-- but I'd like to keep compatibility with GHC 7.6 for now.

-- These functions encapsulate vtable lookup.
targetHeader :: (?tgt::TargetLanguage) => String -> Doc
targetHeader   = _targetHeader   ?tgt

-- It would be nice if we could just say
--    targetHeader = _targetHeader (?tgt::TargetLanguage)
-- and avoid duplicating the types of the record fields.
-- Oh well.

targetFilename  :: (?tgt::TargetLanguage) => String -> String
targetFilename  = _targetFilename ?tgt
targetCall      :: (?tgt::TargetLanguage) => [Doc] -> Doc
targetCall      = _targetCall ?tgt
targetAtomCall  :: (?tgt::TargetLanguage) => [Doc] -> Doc
targetAtomCall  = _targetCall ?tgt
match           :: (?tgt::TargetLanguage) => String -> [(Doc, Doc)] -> Doc
match           = _targetMatch ?tgt
doblock         :: (?tgt::TargetLanguage) => [Doc] -> Doc
doblock         = _targetDoblock ?tgt
doerror         :: (?tgt::TargetLanguage) => String -> Doc
doerror         = _targetDoerror ?tgt
ifthen          :: (?tgt::TargetLanguage) => Doc -> Doc -> Doc -> Doc
ifthen          = _targetIfthen ?tgt
comment         :: (?tgt::TargetLanguage) => Doc -> Doc
comment         = _targetMultiLineComment ?tgt
letbinds        :: (?tgt::TargetLanguage) => [(String, Doc)] -> Doc
letbinds        = _targetLetbinds ?tgt
fnDefinition    :: (?tgt::TargetLanguage) => Doc -> [Doc] -> [Doc] -> Doc -> Doc -> Doc
fnDefinition    = _targetFnDefinition ?tgt
emitAdd         :: (?tgt::TargetLanguage) => String -> String -> Doc
emitAdd         = _targetEmitAdd ?tgt
emitMul         :: (?tgt::TargetLanguage) => String -> String -> Doc
emitMul         = _targetEmitMul ?tgt
emitListLength  :: (?tgt::TargetLanguage) => Doc -> Doc
emitListLength  = _targetEmitListLength ?tgt
emitIO          :: (?tgt::TargetLanguage) => String -> Doc
emitIO          = _targetEmitIO ?tgt
emitBinder      :: (?tgt::TargetLanguage) => String -> Doc
emitBinder      = _targetEmitBinder ?tgt
cgFieldSlotType :: (?tgt::TargetLanguage) => Type_ -> CG Doc
cgFieldSlotType = _targetCgFieldSlotType ?tgt

data TargetLanguage = TargetLanguage {
    _targetHeader   :: String -> Doc
  , _targetFilename :: String -> String
  , _targetCall     :: [Doc]  -> Doc
  , _targetAtomCall :: [Doc]  -> Doc
  , _targetDoblock  :: [Doc]  -> Doc
  , _targetDoerror  :: String -> Doc
  , _targetMatch    :: String -> [(Doc, Doc)] -> Doc
  , _targetIfthen   :: Doc -> Doc -> Doc -> Doc
  , _targetMultiLineComment :: Doc -> Doc
  , _targetLetbinds         :: [(String, Doc)] -> Doc
  , _targetFnDefinition     :: Doc -> [Doc] -> [Doc] -> Doc -> Doc -> Doc
  , _targetEmitAdd          :: String -> String -> Doc
  , _targetEmitMul          :: String -> String -> Doc
  , _targetEmitListLength   :: Doc    -> Doc
  , _targetEmitIO           :: String -> Doc
  , _targetEmitBinder       :: String -> Doc
  , _targetCgFieldSlotType  :: Type_  -> CG Doc
}
-- }}}

-- {{{ Encapsulation of Haskell syntax
targetHaskell = TargetLanguage
                  hsTargetHeader hsTargetFilename hsTargetCall
                  hsAtomCall hsDoblock hsDoerror hsMatch
                  hsIfthen hsMultiLineComment
                  hsLetbinds hsFnDefinition hsEmitAdd
                  hsEmitMul hsEmitListLength hsEmitIO
                  hsEmitBinder hscgFieldSlotType
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
    hsTargetCall (callee:docs) = group $ parens (callee <+> align (vsep docs))
    hsDoblock stmts = text "do" <$> indent 2 (vcat stmts)
    hsDoerror str   = text "error $" <+> text (show str)
    hsMatch var arms =
         align $  text "case" <+> text var <+> text "of"
              <$> indent 2 (vcat [pat <+> text "->" <+> body | (pat, body) <- arms])
    hsIfthen cnd bdy elz = parens (text "if" <+> cnd
                              <$> align (vsep [text "then" <+> bdy
                                              ,text "else" <+> elz]))
    hsAtomCall (callee:txts) = parens (hsep (callee:txts))

    hsMultiLineComment doc = group $ vsep [text "{-", doc, text "-}"]

    hsLetbinds :: [(String, Doc)] -> Doc
    hsLetbinds bindings = vcat [text "let" <+> hsEmitBinder name <+> text "=" <+> body
                               | (name, body) <- bindings]

    hsEmitAdd s1 s2 = hsTargetCall [text s1, text "`plusOffset`", text s2]
    hsEmitMul s1 s2 = hsTargetCall [text s1, text "`mulOffset`",  text s2]
    hsEmitListLength obj = hsTargetCall [text "fromIntegral", hsTargetCall [text "length", obj]]
    hsEmitIO str = text $ "IO " ++ str
    hsEmitBinder str = text $ "!" ++ str -- Make all binders strict in generated code!

    hsFnDefinition name args argtypes retty body =
      let defn = name <+> hsep args <+> text "=" <$> indent 2 body <$> text "" in
      let decl = name <+> text "::" <+> encloseSep empty empty (text " -> ") (argtypes ++ [retty]) in
      case argtypes of
        [] ->          defn
        _  -> decl <$> defn

    hscgFieldSlotType type_ =
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
          Type_Text        -> return $ text "(ByteString, ())"
          Type_Data        -> return $ text "ByteString"
          Type_List      t -> liftM (\tx -> text "[" <> tx <> text "]") (hscgFieldSlotType t)
          Type_Enum      w -> liftM text (lookupId w)
          Type_Struct    w -> liftM text (lookupId w)
          Type_Interface w -> liftM text (lookupId w)
          Type_Object      -> return $ text "<...object...>"

--- }}}

txCall txts = targetCall txts
srCall strs = targetCall (map text strs)

tyOffset = "Int"

data CG_State =
     CG_State (Map Word64 String)
              (Map Word64 Word16)

type CG t = State CG_State t

cgCodeGeneratorRequest :: (?tgt::TargetLanguage) => CodeGeneratorRequest -> CG Doc
cgCodeGeneratorRequest cgr = do
    -- Build the mapping of node ids to type names for later pretty-printing.
    mapM_ denoteNodeAttributes (cgrNodes cgr)

    -- Emit the data type declaration for each node.
    let productiveNodes = filter isNodeProductive (cgrNodes cgr)
    ns <- mapM cgNode productiveNodes

    -- Emit builders and serializers for each node.
    builders    <- mapM emitNodeBuilder    productiveNodes
    serializers <- mapM emitNodeSerializer productiveNodes
    return $ vsep $ ns ++ builders ++ serializers
 where
    denoteNodeAttributes node = do
      denoteNodeId node
      case nodeUnion node of
        ns@(NodeStruct {}) -> do
          denoteStructEncodingTag (nodeId node)
                                  (nodeStruct_preferredListEncoding ns)
        _ -> return ()
    denoteNodeId node = do
      denoteId (nodeId node) (nodeDisplayName node)

    isNodeProductive node =
      case nodeUnion node of
        NodeFile -> False
        NodeAnnotation {} -> False
        _ -> True

    emitNodeSerializer node =
      emitNodeUnionSerializer (nodeUnion node) (nodeDisplayName node) (nodeId node)

    emitNodeBuilder node =
      emitNodeUnionBuilder    (nodeUnion node) (nodeDisplayName node) (nodeId node)

-- {{{ Serializing individual nodes (structs, enums, etc):

emitNodeUnionSerializer node@(NodeStruct {}) dname nodeid | nodeStruct_isGroup node == 0 = do
  let sizedata = nodeStruct_dataWordCount node
  let size     = nodeStruct_pointerCount node + sizedata
  let fnname   = serializerForType (Type_Struct nodeid)
  -- data fields first, then pointer fields
  return $
        fnDefinition (text $ "sr" ++ dname) (splitArgs "obj") [text dname] (retTy (emitIO "ByteString"))
                     (txCall [text "serializeWith", text "obj", fnname])
    <$> fnDefinition fnname (splitArgs "obj rab ptr_off data_off")
                     (map text [dname, "ResizableArrayBuilder", tyOffset, tyOffset]) (retTy (emitIO "()"))
                     (doblock [letbinds [("nextoffset", emitAdd "data_off" (show (8 * size)))]
                              ,srCall (split " " $ helperForStructSerializer nodeid ++ " obj rab data_off nextoffset")
                              ,srCall ["sr_ptr_struct", "rab", "ptr_off", show sizedata, show (size - sizedata),
                                            show (txCall [text "delta_in_words", text "data_off",
                                                          emitAdd "ptr_off" "8"])]])
    <$> comment (text $ "Serialize the given object to data_off, with sub-objects serialized to nextoffset")
    <$> fnDefinition (text (helperForStructSerializer nodeid))
                     (splitArgs "obj rab data_off nextoffset") noArgTys noRetTy
                     (doblock [
                          letbinds [("ptrs_off", emitAdd "data_off" (show (8 * sizedata)))]
                         ,if nodeStruct_discriminantCount node == 0
                            then vcat (map (emitFieldSerializer dname) (nodeStruct_fields node))
                            else
                                let indiscriminantFields = [f | f <- nodeStruct_fields node, fieldDiscriminant f == 0xffff] in
                                let discriminatedFields  = [f | f <- nodeStruct_fields node, fieldDiscriminant f /= 0xffff] in
                                letbinds [("absDiscrimOff", emitAdd "data_off"
                                                                (show $ 2 * nodeStruct_discriminantOffset node))]
                            <$> match "obj" [(text (fieldCtorName dname f) <+> text "{}"
                                              ,doblock $ [srCall ["rabWriteWord16", "rab", "absDiscrimOff", show (fieldDiscriminant f)]
                                                        ,emitFieldSerializer dname f] ++
                                                        (map (emitFieldSerializer dname) indiscriminantFields))
                                                  | f <- discriminatedFields]
                       ])
    <$> fnDefinition (serializerForType (Type_List $ Type_Struct nodeid))
                     (splitArgs "objs rab ptr_off data_off")
                     (map text ["[" ++ dname ++ "]", "ResizableArrayBuilder", tyOffset, tyOffset]) (retTy (emitIO "()"))
         (doblock [
            case nodeStruct_preferredListEncoding node of
             7 ->  letbinds [("objsize", text $ show (size * 8))
                            ,("num_elts", emitListLength $ text "objs")
                            ,("totalsize", emitMul "objsize" "num_elts")
                            ,("num_words", emitMul (show size) "num_elts")
                            ,("target_off", emitAdd "data_off" "8" <+> comment (text "accounting for tag word"))
                            ]
                   <$> srCall ["sr_composite_list_helper", "rab", "objsize", "target_off",
                                 "(target_off + totalsize)", "objs", helperForStructSerializer nodeid]
                   <$> srCall ["sr_ptr_struct", "rab", "data_off", show sizedata, show (size - sizedata), "num_elts"]
                   <$> txCall [text "sr_ptr_list", text "rab", text "ptr_off", text "7", text "num_words",
                                  txCall [text "delta_in_words", text "data_off",
                                           emitAdd "ptr_off" "8"]]
             1 -> error $ "Can't yet support serialization of lists of single-bit structs."
             siz ->
                       --text ("let objsize = " ++ show ((byteSizeOfListEncoding siz) * 8) ++ " :: Word64")
                       text  "-- TODO test this..."
                   <$> letbinds [("objsize", text (show (byteSizeOfListEncoding siz)))
                                ,("num_elts", srCall ["objsLength", "objs"])
                                ,("totalsize", txCall [text "sr_total_size_for", pretty (show siz), pretty (show $ size * 8), text "num_elts"])
                                ]
                   <$> txCall [text "sr_composite_list_helper", text "rab", text "objsize", text "data_off",
                                 emitAdd "data_off" "totalsize", text "objs", text (helperForStructSerializer nodeid)]
                   <$> txCall ((map text ["sr_ptr_list", "rab", "ptr_off", show siz, "num_elts"])
                                        ++ [txCall [text "delta_in_words", text "data_off", emitAdd "ptr_off" "8"]])])

emitNodeUnionSerializer node@(NodeStruct {}) dname nodeid | nodeStruct_isGroup node /= 0 && nodeStruct_discriminantCount node == 0 = do
  let sizedata = nodeStruct_dataWordCount node
  let size    =  nodeStruct_pointerCount node + sizedata
  return $
    fnDefinition (serializerForGroup nodeid)
                 (map text ["!rab", "!obj", "!nextoffset", "!data_off", "!ptrs_off"]) noArgTys noRetTy
              (doblock $ (letbinds [("nextoffset", emitAdd "data_off" (show (8 * size)))])
                         :map (emitFieldSerializer dname) (nodeStruct_fields node))

emitNodeUnionSerializer node@(NodeStruct {}) dname nodeid | nodeStruct_isGroup node /= 0 && nodeStruct_discriminantCount node > 0 = do
  return $
    fnDefinition (serializerForGroup nodeid)
                 (map text ["rab", "obj", "nextoffset", "data_off", "ptrs_off"])
                 noArgTys noRetTy
                 (doblock [letbinds [("absDiscrimOff", emitAdd "data_off" (show (2 * (nodeStruct_discriminantOffset node))))]
                          ,match "obj" [
                             (text (fieldCtorName dname f) <+> text "{}",
                              doblock [srCall ["rabWriteWord16", "rab", "absDiscrimOff", show (fieldDiscriminant f)]
                                      ,emitFieldSerializer dname f])
                             | f <- nodeStruct_fields node]])

emitNodeUnionSerializer node@(NodeEnum {}) dname nodeid = do
  let fnname = serializerForType (Type_Enum nodeid)
  return $ fnDefinition fnname (splitArgs "rab e offset")
                        [text "ResizableArrayBuilder", text dname, text tyOffset] (retTy (emitIO "()"))
              (doblock [letbinds [("value",
                               match "e"
                                [ (text (capitalizeFirstLetter $ legalizeIdent $ enumerantName en)
                                  ,pretty (enumerantOrder en))
                                | en <- nodeEnum_enumerants node])]
                       ,srCall (split " " "rabWriteWord16 rab offset value")])

emitNodeUnionSerializer node dname nodeid = do
  return $ comment $ string (show (dname, nodeid, node))

-------------------------------

-- Individual bits must be specially serialized, because their offsets
-- are measured in bits, not bytes.
emitFieldSerializer typename f | (FieldSlot offsetInBits Type_Bool _) <- fieldUnion f =
  (txCall [serializerForFieldType f Type_Bool,
              text "rab", srCall [getFieldAccessor typename f, "obj"],
              text "data_off", pretty offsetInBits])
     <+> comment (text "serialize bool field" <+> quotedStr (fieldName_ f))

emitFieldSerializer typename f | (FieldSlot w t _) <- fieldUnion f =
  let offsetInBytes = fromIntegral w * byteSizeOfType t in
  (case kindOfType t of
    KindPtr ->
      txCall [serializerForFieldType f t,
                     srCall [getFieldAccessor typename f, "obj"],
                     text "rab",  (emitAdd "ptrs_off" (show offsetInBytes)), text "nextoffset"]
      <$> text "nextoffset <- updateNextOffset rab nextoffset ; return ()"
    KindData ->
      txCall [serializerForFieldType f t, text "rab", srCall [getFieldAccessor typename f, "obj"],
              (emitAdd "data_off" (show offsetInBytes))]
    ) <+> comment (text "serialize field" <+> quotedStr (fieldName_ f) <+> pretty w <+> text "*" <+> pretty (byteSizeOfType t) <+> pretty t)

emitFieldSerializer typename f | (FieldGroup w) <- fieldUnion f =
  txCall [serializerForGroup w,
          text "rab", srCall [getFieldAccessor typename f, "obj"],
          text "nextoffset", text "data_off", text "ptrs_off"]
    <+> comment (text $ "serialize group '" ++ fieldName_ f ++ "'")

getFieldAccessor typename f =
  if fieldDiscriminant f /= 0xffff
    then fieldUnCtorName typename f
    else fieldName       typename f

serializerForFieldType f t =
  if isFieldOptional f
    then txCall [text "sr_Maybe", serializerForType t]
    else serializerForType t
-- }}}

-- {{{
emitNodeUnionBuilder node@(NodeStruct {}) dname nodeid | nodeStruct_discriminantCount node /= 0 = do
  let fnname = makerForType (Type_Struct nodeid)
  let indiscriminantFields = [f | f <- nodeStruct_fields node, fieldDiscriminant f == 0xffff]
  let discriminatedFields =  [f | f <- nodeStruct_fields node, fieldDiscriminant f /= 0xffff]
  fieldAccessors <- mapM (emitGroupFieldAccessor dname indiscriminantFields) discriminatedFields
  let discoffb = nodeStruct_discriminantOffset node * 2
  let args = [text "obj"]
  return $  fnDefinition (text $ "mk" ++ dname) args noArgTys noRetTy (txCall [fnname, text "obj"])
        <$> fnDefinition fnname [text "obj@(StructObj bs ptrs)"] [text "Object"] (retTy $ text dname)
                      (ifthen (srCall ["isDefaultObj", "obj"])
                         (doerror $ "Unset value in non-optional field of type " ++ show dname)
                         (match (show (extractData Type_UInt16 discoffb))
                            [(text (show d), fieldAccessor)
                            | (d, fieldAccessor) <- zip (map fieldDiscriminant discriminatedFields) fieldAccessors]))

emitNodeUnionBuilder node@(NodeStruct {}) dname nodeid = do
  let fnname = makerForType (Type_Struct nodeid)
  fieldAccessors <- mapM emitFieldAccessor (nodeStruct_fields node)
  return $  fnDefinition (text $ "mk" ++ dname) [text "obj"] [text "Object"] (retTy $ text dname)
                         (txCall [fnname, text "obj"])
        <$> fnDefinition fnname [text "obj@(StructObj bs ptrs)"] [text "Object"] (retTy $ text dname)
                         (ifthen (srCall ["isDefaultObj", "obj"])
                           (doerror $ "Unset value in non-optional field of type " ++ show dname)
                           (doblock [txCall (text dname:fieldAccessors)]))

emitNodeUnionBuilder node@(NodeEnum {}) dname nodeid = do
  let fnname = "mk_enum_" ++ show nodeid
  return $  fnDefinition (text fnname) [emitBinder "wx"] [text "Word16"] (retTy $ text dname)
                         (match "wx"
                            [(text (show (enumerantOrder en))
                             ,text (capitalizeFirstLetter $ legalizeIdent $ enumerantName en))
                           | en <- nodeEnum_enumerants node])

emitNodeUnionBuilder other dname _ = do
  let fnname = "mk" ++ dname
  return $  fnDefinition (text fnname) [emitBinder "objx"] [text "Object"] (retTy $ text dname)
                         (srCall [dname, "objx"])

emitGroupFieldAccessor typename commonFields f = do
  accs <- mapM emitFieldAccessor (commonFields ++ [f])
  return $ txCall ((text (fieldCtorName typename f)) : accs)

emitFieldAccessor f | FieldSlot w t v <- fieldUnion f = do
  case kindOfType t of
    KindPtr -> do
      let offset = fromIntegral w
      return $ extractPtr f (show t) t offset <+> comment (text (show t))

    KindData -> do
      let offset = fromIntegral w * byteSizeOfType t
      return $ extractData t offset <+> comment (text (show t))

emitFieldAccessor f | FieldGroup w <- fieldUnion f = do
  return $ txCall [makerForType (Type_Struct w), text "obj"]

------------------------------------------------------------------------

extractData :: (?tgt::TargetLanguage, Show num) => Type_ -> num -> Doc
extractData t offset =
  let accessor = srCall ["at", accessorNameForType t, show offset, "bs"] in
  case t of
    Type_Bool   -> srCall [accessorNameForType t, show offset, "bs"]
    Type_Enum w -> parens $ text ("mk_enum_" ++ show w) <+> accessor
    _           -> accessor

extractPtr :: (?tgt::TargetLanguage) => Field -> String -> Type_ -> Int -> Doc
extractPtr f msg t offset =
  parens $
    case t of
     Type_Text        -> txCall [extractPtrFunc t, ptr]
     Type_Data        -> txCall [extractPtrFunc t, ptr]
     Type_List      x -> txCall [text "mapL",  text ("\"" ++ show x ++ "\""), extractPtrFunc x, ptr]
     Type_Struct    _ -> txCall [extractPtrFunc t, ptr]
     Type_Interface _ -> text "<unsupported extractPtr type:" <+> text (show t)
     Type_Object      -> text "<unsupported extractPtr type:" <+> text (show t)
     _ -> error $ "extractPtr saw unexpected type " ++ show t
 where
   ptr = srCall ["lookupPointer", show msg, "ptrs", show offset]
   wrapper d = if isFieldOptional f then txCall [text "_mkMaybe", d]
                                    else                          d
   extractPtrFunc t =
     wrapper $ case t of
        Type_Text        -> text "unText"
        Type_Data        -> text "unBytes"
        Type_List      x -> error $ "xPF List of " ++ show x
        Type_Struct    _ -> makerForType t
        Type_Interface _ -> error "xPF Interface"
        Type_Object      -> error "xPF Object"
        Type_Void        -> text "mk_void"
        Type_Bool        -> text "mk_Bool"
        Type_UInt64      -> text "mk_Word64"
        Type_Int64       -> text "mk_Int64"
        Type_UInt32      -> text "mk_Word32"
        Type_Int32       -> text "mk_Int32"
        Type_UInt16      -> text "mk_Word16"
        Type_Int16       -> text "mk_Int16"
        Type_UInt8       -> text "mk_Word8"
        Type_Int8        -> text "mk_Int8"
        _ -> error $ "extractPtrFunc saw unexpected type " ++ show t
-- }}}

makerForType (Type_Enum   w) = text $ "mk_enum_"   ++ show w
makerForType (Type_Struct w) = text $ "mk_struct_" ++ show w
makerForType other = error $ "makerForType " ++ show other
{-
makerForType (Type_List (Type_Struct w)) = text $ "mk_list_of_" ++ show w
makerForType (Type_List (Type_Enum   w)) = text $ "mk_list_of_" ++ show w
makerForType (Type_List t) = text $ "mk_list_of_" ++ show t
makerForType t = text ("mk_" ++ show t)
-}

serializerForType (Type_Enum   w) = text $ "sr_enum_"   ++ show w
serializerForType (Type_Struct w) = text $ "sr_struct_" ++ show w
serializerForType (Type_List (Type_Struct w)) = text $ "sr_list_of_" ++ show w
serializerForType (Type_List (Type_Enum   w)) = text $ "sr_list_of_" ++ show w
serializerForType (Type_List t) = text $ "sr_list_of_" ++ show t
serializerForType t = text ("sr_" ++ show t)

serializerForGroup w = text $ "sr_group_" ++ show w

helperForStructSerializer nodeid = "sr_struct_helper_" ++ show nodeid

noArgTys = []
noRetTy = empty
retTy d = d

splitArgs args = map emitBinder $ split " " args
splitTys  args = map text       $ split " " args


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
  where
      spanList _ [] = ([],[])
      spanList func list@(x:xs) =
          if func list
            then (x:ys,zs)
            else ([],list)
          where (ys,zs) = spanList func xs

      breakList :: ([a] -> Bool) -> [a] -> ([a], [a])
      breakList func = spanList (not . func)

sjoin delim s = concat (intersperse delim s)
replace old new s = sjoin new . split old $ s
legalizeTypeName fs = case split ":" fs of
                        [_, s] -> replace "." "_" s
                        [s]    -> replace "." "_" s

capitalizeFirstLetter [] = []
capitalizeFirstLetter (h:t) = toUpper h : t

legalizeIdent "type" = "type_"
legalizeIdent "id"   = "id_"
legalizeIdent str = str

cgNode :: (?tgt::TargetLanguage) => Node -> CG Doc
cgNode node = do
    arms <- computeDataArms (nodeDisplayName node) (nodeUnion node)
    return $ formatDataDecl (nodeDisplayName node) (nodeId node) arms

computeDataArms :: (?tgt::TargetLanguage) => String -> NodeUnion -> CG [(Doc, [Doc])]
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

cgFieldUnion f (FieldGroup w)    = do liftM text (lookupId w)
cgFieldUnion f (FieldSlot _ t _) = do ty <- cgFieldSlotType t
                                      if isFieldOptional f
                                        then return $ parens $ text "StrictMaybe" <+> ty
                                        else return ty
formatDataDecl name nodeid arms =
      comment (pretty nodeid)
  <$> text "data" <+> text name <+> text "="
        <$> indent 4 (cases (map formatDataArm arms)
                      <$> text "deriving Show")
        <$> text ""
  where
      cases :: [Doc] -> Doc
      cases []         = text ""
      cases [doc]      = doc
      cases (doc:docs) = vsep $ (text " " <+> doc) : (map (\d -> text "|" <+> d) docs)

      formatDataArm (armName, []) = armName
      formatDataArm (armName, armFields) =
        armName <+> text "{"
          <$> indent 4 (embedded armFields)
          <$> text "}"

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

byteSizeOfListEncoding n =
  case n of
    2 -> 1
    3 -> 2
    4 -> 4
    5 -> 8
    6 -> 8
    _ -> error $ "byteSizeOfListEncoding requires n to be [2..6]; had " ++ show n

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

nodeDisplayName n = legalizeTypeName $ nodeDisplayName_ n

quoted d = squote <> d <> squote
quotedStr s = quoted (text s)

instance Pretty Word16 where pretty w = text (show w)
instance Pretty Word32 where pretty w = pretty (show w)
instance Pretty Type_  where pretty w = pretty (show w)

