{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# HLINT ignore "Use camelCase" #-}

{-- The ClassPath module provide access to Java .class files in the classpath. Data from these classes
    is required by the compiler. A ClassPath type provides map from package names to a second map from
    type names to a reference to the type byte code (in a Directory or Jar file). Once the byte code for
    a type has been loaded an parsed in the a ClassDescriptor, the ClassDescriptors are stored in another
    map in the ClassPath. This classMap serves as a cache for ClassDescriptors and is always consulted
    first before looking in the referenceMap. 
-}
module ClassPath
( ClassPath
, ClassDescriptor(..)
, Field(..)
, Method(..)
, createClassPath
, getClass
, hasClass
, getPackageClasses
, main
) where

import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as V hiding (Vector)
import System.IO (IOMode(..),Handle, withBinaryFile)
import qualified Data.ByteString.Lazy as B
import Data.ByteString.Builder ( toLazyByteString, word32BE )
import Data.Word ( Word8, Word16, Word32, Word64 )
import Data.Binary ( decode )
import qualified Data.Text as T
import Data.List ( find, elemIndices )
import Data.Text.Encoding (decodeUtf8)
import Data.List.Split (splitOn)
import System.FilePattern.Directory (getDirectoryFiles)
import Control.Monad (foldM)
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.State.Strict as ST
import Debug.Trace ()

type ClassReferenceMap = Map.Map T.Text ClassReference

type PackageMap = Map.Map T.Text ClassReferenceMap

data ClassPath = ClassPath { directories :: [T.Text]
                           , jars :: [T.Text]
                           , referenceMap :: PackageMap
                           , classMap :: Map.Map T.Text ClassDescriptor
                           } deriving Show

data ClassReference = DirectoryReference T.Text | JarReference T.Text deriving (Show)

data ClassDescriptor = ClassDescriptor { name :: T.Text
                                       , parent :: T.Text
                                       , fields :: [Field]
                                       , methods :: [Method]
                                       }

data Field = Field { fname :: T.Text
                   , ftype :: T.Text
                   , faccess_flags :: Word16
                   }

data Method = Method { mname :: T.Text
                     , mdescriptor :: T.Text
                     , maccess_flags :: Word16
                     }

data ClassFile = ClassFile { minor_version :: !Word16
                           , major_version :: !Word16
                           , constant_pool :: Vector Cp_info
                           , access_flags :: !Word16
                           , this_class :: Int
                           , super_class :: Int
                           , interfaces :: Vector CONSTANT_Class_info
                           , fields_info :: Vector Field_info
                           , methods_info :: Vector Method_info
                           } deriving (Show)

data Cp_info = ClassInfo CONSTANT_Class_info
             | Utf8Info CONSTANT_Utf8_info
             | NameAndTypeInfo CONSTANT_NameAndType_info
             | FieldrefInfo CONSTANT_Fieldref_info
             | MethodrefInfo CONSTANT_Methodref_info
             | InterfaceMethodrefInfo CONSTANT_InterfaceMethodref_info
             | ConstantStringInfo CONSTANT_String_info
             | ConstantIntegerInfo CONSTANT_Integer_info
             | ConstantFloatInfo CONSTANT_Float_info
             | ConstantLongInfo CONSTANT_Long_info
             | ConstantDoubleInfo CONSTANT_Double_info
             | Empty
             deriving (Show)

newtype CONSTANT_Class_info = CONSTANT_Class_info { ci_name_index :: Int
                                               } deriving (Show)

newtype CONSTANT_Utf8_info = CONSTANT_Utf8_info { u_text :: T.Text
                                             } deriving (Show)

data CONSTANT_NameAndType_info = CONSTANT_NameAndType_info { nt_name_index :: Int
                                                           , nt_descriptor_index :: Int
                                                           } deriving (Show)

data CONSTANT_Fieldref_info = CONSTANT_Fieldref_info { fri_class_index :: Int
                                                     , fri_name_and_type_index :: Int
                                                     } deriving (Show)

data CONSTANT_Methodref_info = CONSTANT_Methodref_info { mri_class_index :: Int
                                                       , mri_name_and_type_index :: Int
                                                       } deriving (Show)

data CONSTANT_InterfaceMethodref_info = CONSTANT_InterfaceMethodref_info { imri_class_index :: Int
                                                                        , imri_name_and_type_index :: Int
                                                                        } deriving (Show)

newtype CONSTANT_String_info = CONSTANT_String_info { s_string_index :: Int } deriving (Show)

newtype CONSTANT_Integer_info = CONSTANT_Integer_info { i_bytes :: Word32 } deriving (Show)

newtype CONSTANT_Float_info = CONSTANT_Float_info { f_bytes :: Word32 } deriving (Show)

newtype CONSTANT_Long_info = CONSTANT_Long_info { l_bytes :: Word64 } deriving (Show)

newtype CONSTANT_Double_info = CONSTANT_Double_info { d_bytes :: Word64 } deriving (Show)

data Field_info = Field_info { fi_access_flags :: !Word16
                             , fi_name_index :: Int
                             , fi_descriptor_index :: Int
                             , fi_attributes_info :: Vector Attribute_info
                             } deriving (Show)

data Method_info = Method_info { mi_access_flags :: !Word16
                               , mi_name_index :: Int
                               , mi_descriptor_index :: Int
                               , mi_attributes_info :: Vector Attribute_info
                               } deriving (Show)

newtype Attribute_info = Attribute_info { attribute_name_index :: Int
                                     } deriving (Show)

getClassFieldType :: ClassDescriptor -> T.Text -> Maybe T.Text
getClassFieldType ClassDescriptor {..} fieldName =
  (\Field {..} -> ftype) <$> Data.List.find (\Field {..} -> fname == fieldName) fields

magicByteString :: [Word8]
magicByteString = B.unpack (toLazyByteString (word32BE 0xCAFEBABE))

sep = T.pack "/"

instance Show ClassDescriptor where
  show ClassDescriptor {..} = "class "++T.unpack name++" extends "++T.unpack parent++"\n"++
                              "Fields:\n"++concat (foldl (\l f -> ("         "++show f++"\n"):l) [] fields)++"\n"++
                              "Methods:\n"++concat (foldl (\l m -> ("          "++show m++"\n"):l) [] methods)++"\n"

instance Show Field where
  show Field {..} = T.unpack ftype++" "++T.unpack fname

instance Show Method where
  show Method {..} = T.unpack mname++" "++T.unpack mdescriptor

readClassFile :: ClassReference -> T.Text -> IO (Maybe ClassFile)
readClassFile (DirectoryReference directory) name = do
  let fp = directory <> sep <> name <> T.pack ".class"
  withBinaryFile (T.unpack fp) ReadMode readClassFile'
readClassFile (JarReference jar) name =
  return Nothing

readClassFile' :: Handle -> IO (Maybe ClassFile)
readClassFile' handle = do
  magic <- B.hGet handle 4
  if magicByteString == B.unpack magic then do
    minor <- B.hGet handle 2
    major <- B.hGet handle 2
    cpCountBytes <- B.hGet handle 2
    let cpCount = (fromIntegral (decode cpCountBytes :: Word16) :: Int)
    cp <- ST.evalStateT (V.replicateM (cpCount-1) (readConstantPoolInfo handle)) False
    access_flags <- getFlags handle
    this_class <- getIndex handle
    super_class <- getIndex handle
    interfaces_count <- getCount handle
    interfaces <- V.replicateM interfaces_count (readClassInfo handle)
    fields_count <- getCount handle
    fields <- V.replicateM fields_count (readFieldInfo handle)
    methods_count <- getCount handle
    methods <- V.replicateM methods_count (readMethodInfo handle)

    return $ Just (ClassFile { minor_version=decode minor :: Word16
                             , major_version=decode major :: Word16
                             , constant_pool=cp
                             , access_flags=access_flags
                             , this_class=this_class
                             , super_class=super_class
                             , interfaces=interfaces
                             , fields_info=fields
                             , methods_info=methods
                             })
  else
    return Nothing

{-- This function requires the state monad because long and double constants consume 2 slots in the constant pool Vector -}
readConstantPoolInfo :: Handle -> ST.StateT Bool IO Cp_info
readConstantPoolInfo handle = do
  isRepeat <- ST.get
  if isRepeat then do
    ST.put False
    return Empty
  else do
    tagByte <- lift $ B.hGet handle 1
    let tag = (fromIntegral (decode tagByte :: Word8) :: Int)
    cpInfo <- lift $ case tag of
      1 -> fmap Utf8Info (readUtf8Info handle)
      3 -> fmap ConstantIntegerInfo (readIntegerInfo handle)
      4 -> fmap ConstantFloatInfo (readFloatInfo handle)
      5 -> fmap ConstantLongInfo (readLongInfo handle)
      6 -> fmap ConstantDoubleInfo (readDoubleInfo handle)
      7 -> fmap ClassInfo (readClassInfo handle)
      8 -> fmap ConstantStringInfo (readStringInfo handle)
      9 -> fmap FieldrefInfo (readFieldrefInfo handle)
      10 -> fmap MethodrefInfo (readMethodrefInfo handle)
      11 -> fmap InterfaceMethodrefInfo (readInterfaceMethodrefInfo handle)
      12 -> fmap NameAndTypeInfo (readNameAndTypeInfo handle)
      _ -> do
        error ("Unsupported constant table type "++show tag)
    if tag == 5 || tag == 6 then do
      ST.put True
      return cpInfo
    else
      return cpInfo

readUtf8Info :: Handle -> IO CONSTANT_Utf8_info
readUtf8Info handle = do
  length <- getCount handle
  bytes <- B.hGet handle length
  let u_text = decodeUtf8 (B.toStrict bytes)
  return $ CONSTANT_Utf8_info {..}

readClassInfo :: Handle -> IO CONSTANT_Class_info
readClassInfo handle = do
  ci_name_index <- getIndex handle
  return $ CONSTANT_Class_info {..}

readNameAndTypeInfo :: Handle -> IO CONSTANT_NameAndType_info
readNameAndTypeInfo handle = do
  nt_name_index <- getIndex handle
  nt_descriptor_index <- getIndex handle
  return $ CONSTANT_NameAndType_info {..}

readFieldrefInfo :: Handle -> IO CONSTANT_Fieldref_info
readFieldrefInfo handle = do
  fri_class_index <- getIndex handle
  fri_name_and_type_index <- getIndex handle
  return $ CONSTANT_Fieldref_info {..}

readMethodrefInfo :: Handle -> IO CONSTANT_Methodref_info
readMethodrefInfo handle = do
  mri_class_index <- getIndex handle
  mri_name_and_type_index <- getIndex handle
  return $ CONSTANT_Methodref_info {..}

readInterfaceMethodrefInfo :: Handle -> IO CONSTANT_InterfaceMethodref_info
readInterfaceMethodrefInfo handle = do
  imri_class_index <- getIndex handle
  imri_name_and_type_index <- getIndex handle
  return $ CONSTANT_InterfaceMethodref_info {..}

readStringInfo :: Handle -> IO CONSTANT_String_info
readStringInfo handle = do
  s_string_index <- getIndex handle
  return $ CONSTANT_String_info {..}

readIntegerInfo handle = do
  bytes <- B.hGet handle 4
  let i_bytes = (decode bytes :: Word32)
  return $ CONSTANT_Integer_info {..}

readFloatInfo handle = do
  bytes <- B.hGet handle 4
  let f_bytes = (decode bytes :: Word32)
  return $ CONSTANT_Float_info {..}

readLongInfo handle = do
  bytes <- B.hGet handle 8
  let l_bytes = (decode bytes :: Word64)
  return $ CONSTANT_Long_info {..}

readDoubleInfo handle = do
  bytes <- B.hGet handle 8
  let d_bytes = (decode bytes :: Word64)
  return $ CONSTANT_Double_info {..}

readFieldInfo :: Handle -> IO Field_info
readFieldInfo handle = do
  fi_access_flags <- getFlags handle
  fi_name_index <- getIndex handle
  fi_descriptor_index <- getIndex handle
  attributesCount <- getCount handle
  fi_attributes_info <- V.replicateM attributesCount (readAttributeInfo handle)
  return $ Field_info {..}

readMethodInfo :: Handle -> IO Method_info
readMethodInfo handle = do
  mi_access_flags <- getFlags handle
  mi_name_index <- getIndex handle
  mi_descriptor_index <- getIndex handle
  attributesCount <- getCount handle
  mi_attributes_info <- V.replicateM attributesCount (readAttributeInfo handle)
  return $ Method_info {..}

readAttributeInfo :: Handle -> IO Attribute_info
readAttributeInfo handle = do
  attribute_name_index <- getIndex handle
  attributeLength <- getLength handle
  info <- B.hGet handle attributeLength
  return $ Attribute_info {..}

getFlags :: Handle -> IO Word16
getFlags handle = do
  bytes <- B.hGet handle 2
  return (decode bytes :: Word16)

getIndex :: Handle -> IO Int
getIndex handle = do
  bytes <- B.hGet handle 2
  return (fromIntegral (decode bytes :: Word16) :: Int)

getCount :: Handle -> IO Int
getCount handle = do
  bytes <- B.hGet handle 2
  return (fromIntegral (decode bytes :: Word16) :: Int)

getLength :: Handle -> IO Int
getLength handle = do
  bytes <- B.hGet handle 4
  return (fromIntegral (decode bytes :: Word32) :: Int)

getClassFromConstantPool :: ClassFile -> Int -> CONSTANT_Class_info
getClassFromConstantPool ClassFile {constant_pool=cp} index =
  let (ClassInfo c) = cp V.! (index - 1) in c

getUtf8FromConstantPool :: ClassFile -> Int -> T.Text
getUtf8FromConstantPool ClassFile {constant_pool=cp} index =
  let (Utf8Info u) = cp V.! (index - 1) in u_text u

createClassDescriptor :: ClassFile -> ClassDescriptor
createClassDescriptor classFile =
  let classInfo = getClassFromConstantPool classFile (this_class classFile)
      name = getUtf8FromConstantPool classFile (ci_name_index classInfo)
      parentClassInfo = getClassFromConstantPool classFile (super_class classFile)
      parent = getUtf8FromConstantPool classFile (ci_name_index parentClassInfo)
      fields = foldl (\list f -> mapField classFile f:list) [] (fields_info classFile)
      methods = foldl (\list m -> mapMethod classFile m:list) [] (methods_info classFile) in
  ClassDescriptor {..}

mapField :: ClassFile -> Field_info -> Field
mapField classFile fi =
  let fname = getUtf8FromConstantPool classFile (fi_name_index fi)
      ftype = getUtf8FromConstantPool classFile (fi_descriptor_index fi)
      faccess_flags = fi_access_flags fi
  in
    Field {..}

mapMethod :: ClassFile -> Method_info -> Method
mapMethod classFile mi =
  let mname = getUtf8FromConstantPool classFile (mi_name_index mi)
      mdescriptor = getUtf8FromConstantPool classFile (mi_descriptor_index mi)
      maccess_flags = mi_access_flags mi
  in
    Method {..}

getClass :: ClassPath -> T.Text -> IO (Maybe ClassDescriptor)
getClass cp qualifiedName = do
  let maybeClass = classMap cp Map.!? qualifiedName
  case maybeClass of
    Just clazz -> return (Just clazz)
    Nothing -> do
      let (package,clazz) = T.breakOnEnd sep qualifiedName
      let maybePackage = referenceMap cp Map.!? package
      let maybeRef = maybePackage >>= (Map.!? clazz)
      case maybeRef of
        Nothing -> return Nothing
        Just ref -> do
          classFile <- readClassFile ref qualifiedName
          return $ fmap createClassDescriptor classFile

hasClass :: ClassPath -> T.Text -> IO Bool
hasClass cp qualifiedName = do
  let (package,clazz) = T.breakOnEnd sep qualifiedName
  return $ Map.member package (referenceMap cp)

getPackageClasses :: ClassPath -> [T.Text] -> Maybe [T.Text]
getPackageClasses cp package =
  let packageText = T.append (T.intercalate sep package) sep in
    getPackageClasses' cp packageText

getPackageClasses' :: ClassPath -> T.Text -> Maybe [T.Text]
getPackageClasses' cp package = do
  let maybePackageMap = referenceMap cp Map.!? package in
    fmap Map.keys maybePackageMap


createClassPath :: String -> IO ClassPath
createClassPath cpString = do
  let cpList = splitOn ":" cpString
  let directories = fmap T.pack cpList
  let jars = []
  referenceMap <- foldM (\result fp -> fmap (Map.unionWith Map.union result) (refMapFromDirectory fp)) Map.empty cpList
  let classMap = Map.empty
  return ClassPath {..}

refMapFromDirectory :: FilePath -> IO PackageMap
refMapFromDirectory directoryPath = do
  let directoryPathReference = DirectoryReference (T.pack directoryPath)
  directoryFiles <- getDirectoryFiles directoryPath ["**/*.class"]
  let mappingList = fmap (\f -> (mapFilePathToQualifiedName f, directoryPathReference)) directoryFiles
  let packageMap = foldl addQualifiedNameToPackageMap Map.empty mappingList
  return packageMap

addQualifiedNameToPackageMap :: PackageMap -> (T.Text, ClassReference) -> PackageMap
addQualifiedNameToPackageMap pm (qn,ref) =
  let (package,clazz) = T.breakOnEnd sep qn in case pm Map.!? package of
    Nothing -> Map.insert package (Map.insert clazz ref Map.empty) pm
    Just _ -> Map.adjust (Map.insert clazz ref) package pm

mapFilePathToQualifiedName :: FilePath -> T.Text
mapFilePathToQualifiedName fp =
  let dotIndices = elemIndices '.' fp in
  case length dotIndices of
    0 -> error "File violating pattern returned"
    _ -> T.pack (take (last dotIndices) fp)

main :: IO ()
main = do
  classPath <- createClassPath "out2:out3/classes"
  maybecf <- getClass classPath (T.pack "java/lang/Integer")
  case maybecf of
    Just cf -> print cf
    Nothing -> putStrLn "Error"
