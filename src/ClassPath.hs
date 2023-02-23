{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}

{-- The ClassPath module provide access to Java .class files in the classpath. Data from these classes
    is required by the compiler. A ClassPath type provides map from package names to a second map from
    type names to a reference to the type byte code (in a Directory or Jar file). Once the byte code for
    a type has been loaded and parsed in the a ClassDescriptor, the ClassDescriptors are stored in another
    map in the ClassPath. This classMap serves as a cache for ClassDescriptors and is always consulted
    first before looking in the referenceMap.

    The ClassPathValidTypeName constructors are private to this module. A ClassPathValidType name serves
    as proof that a type name represents a valid classpath type. 
-}
module ClassPath
( ClassPath
{--, ClassPathValidTypeName -- No constructors exported for this type by design-}
, ClassPathType
, ClassDescriptor(..)
, Field(..)
, Method(..)
, createClassPath
, getClassPathValidType
, getClassPathClassType
, hasClass
, isClassPathTypeBoolean
, isClassPathTypeInteger
, getClassPathTypeReference
, getClassPathTypeVariable
, getPackageClasses
, mapMethodToParamTypeList
, mapMethodToResultType
, cInterfaceMaskedValue
, cAbstractMaskedValue
, cPublicMaskedValue
, fStaticMaskedValue
, mStaticMaskedValue
, mAbstractMaskedValue
, mSyncheticMaskedValue
, mBridgeMaskedValue
, createValidTypeNameObject
, createValidTypeRefTypeObject
, createValidTypeClassTypeObject
, createValidTypeNameInteger
, createValidTypeRefTypeInteger
, createValidTypeClassTypeInteger
, createValidTypeNameBoolean
, createValidTypeRefTypeBoolean
, createValidTypeClassTypeBoolean
, createValidTypeNameString
, createValidTypeRefTypeString
, createValidTypeClassTypeString
) where

import qualified Data.Map.Strict as Map
import Data.Vector (Vector)
import qualified Data.Set as S
import qualified Data.Either as E
import qualified Data.Vector as V hiding (Vector)
import Data.Maybe (fromMaybe)
import System.IO (IOMode(..),Handle, withBinaryFile,hPutStrLn,stderr)
import System.Exit ( ExitCode(ExitFailure), exitWith )
import qualified Control.Exception as E
import qualified Data.ByteString.Lazy as B
import Data.ByteString.Builder ( toLazyByteString, word32BE )
import Data.Word ( Word8, Word16, Word32, Word64 )
import Data.Binary ( decode )
import qualified Data.Text as T
import Data.List ( find, elemIndices, foldl', intercalate )
import Data.Text.Encoding (decodeUtf8)
import Data.List.Split (splitOn)
import System.FilePattern.Directory (getDirectoryFiles)
import Control.Monad (foldM)
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.State.Strict as ST
import TextShow (TextShow(showt),showb,toText )
import Debug.Trace (trace, traceStack)
import Control.Monad.Trans.State.Strict (StateT,get,put,evalStateT)
import Control.Monad.Extra (join)
import Text.Parsec ( anyChar, char, manyTill, (<|>), oneOf, lookAhead, optionMaybe, char, many1, many, spaces, runParser, Parsec )
import Data.Bits ( Bits(bit) )
import qualified Data.FlagSet as FS
import TypeCheckerTypes
import Data.ByteString (ByteString)
import qualified Data.IntMap.Strict as List

type ClassReferenceMap = Map.Map T.Text ClassReference

classPathValidTypeName :: QualifiedName -> TypeCheckerValidTypeQualifiedNameWrapper
classPathValidTypeName qn = TypeCheckerValidTypeQualifiedNameWrapper { getValidTypeQName = qn
                                                                     }
data JavaTypeSignature = PrimitiveJavaTypeSignature !ClassPathType
                       | ReferenceJavaTypeSignature !TypeCheckerReferenceTypeWrapper
                       deriving (Show,Eq)

type PackageMap = Map.Map T.Text ClassReferenceMap -- Mapping from qualified name to the class bytes reference

data ClassPath = ClassPath { directories :: ![T.Text]
                           , jars :: ![T.Text]
                           , referenceMap :: !PackageMap
                           , classMap :: !(Map.Map T.Text ClassDescriptor)
                           }

data ClassReference = DirectoryReference T.Text | JarReference T.Text deriving (Show)

data ClassDescriptor = ClassDescriptor { name :: !TypeCheckerValidTypeQualifiedNameWrapper
                                       , parent :: !TypeCheckerClassReferenceTypeWrapper
                                       , accessFlags :: FS.T Word16 ClassAccessFlag
                                       , typeParameters :: !(Vector TypeCheckerTypeParameter)
                                       , interfaceClasses :: !(S.Set TypeCheckerClassReferenceTypeWrapper)
                                       , fields :: ![Field]
                                       , methods :: ![Method]
                                       }

data Field = Field { fname :: !T.Text
                   , ftype :: ClassPathType
                   , faccessFlags :: FS.T Word16 FieldAccessFlag
                   , fclassTypeParameters :: Vector TypeCheckerTypeParameter
                   , fcClassName :: !TypeCheckerValidTypeQualifiedNameWrapper
                   }

data Method = Method { mname :: !T.Text
                     , mdescriptor :: !T.Text
                     , maccessFlags :: FS.T Word16 MethodAccessFlag
                     , mclassTypeParameters :: Vector TypeCheckerTypeParameter
                     , mcClassName :: !TypeCheckerValidTypeQualifiedNameWrapper
                     }

data ClassFile = ClassFile { minor_version :: !Word16
                           , major_version :: !Word16
                           , constant_pool :: Vector Cp_info
                           , access_flags :: !Word16
                           , this_class :: !Int
                           , super_class :: !Int
                           , interfaces :: Vector Int
                           , fields_info :: Vector Field_info
                           , methods_info :: Vector Method_info
                           , attributes_info :: Vector Attribute_info
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
             | MethodHandleInfo CONSTANT_MethodHandle_info
             | MethodTypeInfo CONSTANT_MethodType_info
             | DynamicInfo CONSTANT_Dynamic_info
             | InvokeDynamicInfo CONSTANT_InvokeDynamic_info
             | CpEmpty
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

data CONSTANT_MethodHandle_info = CONSTANT_MethodHandle_info { mh_reference_kind :: Word8
                                                             , mh_reference_index :: Int
                                                             } deriving Show

data CONSTANT_MethodType_info = CONSTANT_MethodType_info { mt_descriptor_index :: Int } deriving Show

data CONSTANT_Dynamic_info = CONSTANT_Dynamic_info { d_bootstrap_method_attr_index :: Int
                                                   , d_name_and_type_index :: Int
                                                   } deriving Show

data CONSTANT_InvokeDynamic_info = CONSTANT_InvokeDynamic_info { id_bootstrap_method_attr_index :: Int
                                                               , id_name_and_type_index :: Int
                                                               } deriving Show

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

data Attribute_info = Attribute_info { attribute_name_index :: Int
                                     , attribute_bytes :: B.ByteString
                                     } deriving (Show)

createValidTypeNameObject = classPathValidTypeName createQNameObject

createValidTypeRefTypeObject =  TypeCheckerClassRefType createValidTypeClassTypeObject

createValidTypeClassTypeObject = TypeCheckerClassReferenceTypeWrapper createValidTypeNameObject Nothing

createValidTypeNameInteger = classPathValidTypeName createQNameInteger

createValidTypeRefTypeInteger = TypeCheckerClassRefType createValidTypeClassTypeInteger

createValidTypeClassTypeInteger = TypeCheckerClassReferenceTypeWrapper createValidTypeNameInteger Nothing

createValidTypeNameBoolean = classPathValidTypeName createQNameBoolean

createValidTypeRefTypeBoolean = TypeCheckerClassRefType createValidTypeClassTypeBoolean

createValidTypeClassTypeBoolean = TypeCheckerClassReferenceTypeWrapper createValidTypeNameBoolean Nothing

createValidTypeNameString = classPathValidTypeName createQNameString

createValidTypeRefTypeString = TypeCheckerClassRefType createValidTypeClassTypeString

createValidTypeClassTypeString = TypeCheckerClassReferenceTypeWrapper createValidTypeNameString Nothing

data ClassPathType =
            I
          | Z
          | V
          | B
          | C
          | D
          | F
          | J
          | S
          | A !ClassPathType
          | L !TypeCheckerClassReferenceTypeWrapper
          | T !SimpleName

instance Show ClassPathType where
  show I = "I"
  show Z = "Z"
  show V = "V"
  show B = "B"
  show C = "C"
  show D = "D"
  show F = "F"
  show J = "J"
  show S = "S"
  show (A t) = "["++show t
  show (L cprt) = show cprt -- show for ClassPathValidTypeName adds 'L' prefix and ';' suffix.
  show (T sn) = "T"++show sn

instance Eq ClassPathType where
  (==) I I = True
  (==) Z Z = True
  (==) V V = True
  (==) B B = True
  (==) C C = True
  (==) D D = True
  (==) F F = True
  (==) J J = True
  (==) S S = True
  (==) (A t) (A t') = t == t'
  (==) (L cprt1) (L cprt2) = cprt1 == cprt2
  (==) (T n1) (T n2) = n1 == n2
  (==) _ _ = False

instance Ord ClassPathType where
  compare a b = compare (show a) (show b)

readType :: T.Text -> ClassPathType
readType t | T.head t == 'I' = I
readType t | T.head t == 'Z' = Z
readType t | T.head t == 'V' = V
readType t | T.head t == 'B' = B
readType t | T.head t == 'C' = C
readType t | T.head t == 'D' = D
readType t | T.head t == 'F' = F
readType t | T.head t == 'J' = J
readType t | T.head t == 'S' = S
readType t | T.head t == '[' = A (readType (T.tail t))
readType t | T.head t == 'L' = L (TypeCheckerClassReferenceTypeWrapper (classPathValidTypeName (constructQualifiedName $ T.drop 1 (T.dropEnd 1 t))) Nothing)
readType t = error ("Unkown type prefix: " ++ T.unpack t)

mapJavaTypeSignatureToClassPathType :: JavaTypeSignature -> ClassPathType
mapJavaTypeSignatureToClassPathType (PrimitiveJavaTypeSignature cpt) = cpt
mapJavaTypeSignatureToClassPathType (ReferenceJavaTypeSignature rts) = mapClassPathReferenceTypeToClassPathType rts

mapClassPathReferenceTypeToClassPathType :: TypeCheckerReferenceTypeWrapper -> ClassPathType
mapClassPathReferenceTypeToClassPathType rts =
  case rts of
    (TypeCheckerClassRefType tccrtw) -> L tccrtw
    TypeCheckerTypeVariableRefType sn -> T sn
    TypeCheckerArrayRefType cprt -> mapCPRT cprt
    where
      mapCPRT cprt' = case cprt' of
        cprt@(TypeCheckerClassRefType _) -> A (mapClassPathReferenceTypeToClassPathType cprt)
        cprt@(TypeCheckerTypeVariableRefType _) -> A (mapClassPathReferenceTypeToClassPathType cprt)
        (TypeCheckerArrayRefType cprt'') -> A (mapCPRT cprt'')

mapMethodToParamTypeList :: Method -> [ClassPathType]

mapMethodToParamTypeList Method {..} =
  let (_,paramTypes,_) = case
          runParser parseMethodSignature () "" (T.unpack mdescriptor)
        of
          Left e -> trace ("Parse descriptor failure: "++T.unpack mdescriptor++show e) undefined
          Right r -> r
  in
    fmap mapJavaTypeSignatureToClassPathType paramTypes


{-- Get an ordered list of type parameters in the field context. Filed context includes
    class type parameters only. 
-}
getFieldContextTypeParameters :: Field -> [TypeCheckerTypeParameter]
getFieldContextTypeParameters Field {..} =
  V.toList fclassTypeParameters

{-- Get an ordered list of type parameters in the method context. Method context includes
    class type parameters followed by method type parameters. 
-}
getMethodContextTypeParameters :: Method -> [TypeCheckerTypeParameter]
getMethodContextTypeParameters Method {..} =
  let (methodTypeParams,_,_) = case
          runParser parseMethodSignature () "" (T.unpack mdescriptor)
        of
          Left e -> trace ("Parse descriptor failure: "++T.unpack mdescriptor++show e) undefined
          Right r -> r
  in
    V.toList mclassTypeParameters ++ methodTypeParams


mapMethodToResultType :: Method -> ClassPathType
mapMethodToResultType Method {..} =
  let (_,_,resultType) = case
          runParser parseMethodSignature () "" (T.unpack mdescriptor)
        of
          Left e -> trace ("Parse descriptor failure: "++T.unpack mdescriptor++show e) undefined
          Right r -> r
  in
    mapJavaTypeSignatureToClassPathType resultType

parseMethodDescriptor :: T.Text -> ([ClassPathType],ClassPathType)
parseMethodDescriptor t =
  let eitherResult = runParser parseMethodDescriptor' () "" (T.unpack t)
  in
    case eitherResult of
      Left e -> trace ("Parse descriptor failure: "++T.unpack t++show e) undefined
      Right r -> r

parseMethodDescriptor' = do
  char '('
  paramTypes <- manyTill (parsePrimitiveType <|> parseArray <|> parseReferenceTypeType) (char ')')
  returnType <- parsePrimitiveType <|> parseArray <|> parseReferenceTypeType
  return (paramTypes,returnType)

parsePrimitiveType :: Parsec String () ClassPathType
parsePrimitiveType = do
  c <- char 'I' <|> char 'Z' <|> char 'V' <|> char 'B' <|> char 'C' <|> char 'D' <|> char 'F' <|> char 'J' <|> char 'S'
  case c of
    'I' -> return I
    'Z' -> return Z
    'V' -> return V
    'B' -> return B
    'C' -> return C
    'D' -> return D
    'F' -> return F
    'J' -> return J
    'S' -> return S
    _ -> undefined

parseArray :: Parsec String () ClassPathType
parseArray = do
  c <- char '['
  t <- parsePrimitiveType <|> parseReferenceTypeType
  return $ A t

parseReferenceTypeSignature =
  fmap
    TypeCheckerClassRefType
    parseCPClassRefType
      <|> parseCPArrayRefType
      <|> parseCPTypeVariableRefType

parseReferenceTypeType = L <$> parseCPClassRefType

parseCPArrayRefType = do
  char '['
  TypeCheckerArrayRefType <$> parseReferenceTypeSignature

parseCPClassRefType = do
  char 'L'
  s <- manyTill anyChar (lookAhead (char ';') <|> lookAhead (char '<'))
  maybeSemi <- optionMaybe (char ';')
  maybeTypeArguments <- case maybeSemi of
    Just _ -> return Nothing
    Nothing -> do
      typeArgs <- parseTypeArguments;
      char ';'
      return $ Just typeArgs
  return (TypeCheckerClassReferenceTypeWrapper (classPathValidTypeName (constructQualifiedName (T.pack s))) maybeTypeArguments)

parseCPTypeVariableRefType = do
  char 'T'
  s <- manyTill anyChar (char ';')
  return $ TypeCheckerTypeVariableRefType $ constructSimpleName (T.pack s)


parseTypeArguments = do
  char '<'
  typeArguments <- many1 (parseAnyTypeArgument <|> parseRefTypeArgument)
  char '>'
  return (V.fromList typeArguments)

parseRefTypeArgument = do
  maybeWildcardChar <- optionMaybe (char '+' <|> char '-')
  let maybeWildcard = case maybeWildcardChar of
        Nothing -> Nothing
        Just c -> case c of
          '+' -> Just ValidTypeWildcardIndicatorExtends
          '-' -> Just ValidTypeWildcardIndicatorSuper
          _ -> undefined
  TypeCheckerTypeArgument maybeWildcard <$> parseReferenceTypeSignature

parseAnyTypeArgument = do
  char '*'
  return $ TypeCheckerTypeArgument
    (Just ValidTypeWildcardIndicatorExtends )
    (TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper (classPathValidTypeName createQNameObject) Nothing))

parseClassSignature ::
  Parsec
  String
  ()
  (Maybe [TypeCheckerTypeParameter], TypeCheckerClassReferenceTypeWrapper, [TypeCheckerClassReferenceTypeWrapper])
parseClassSignature = do
  typeParams <- optionMaybe parseTypeParameters
  parentTypeSig <- parseCPClassRefType
  interfaceRefTypes <- many parseCPClassRefType
  return (typeParams,parentTypeSig,interfaceRefTypes)

parseTypeParameters = do
  char '<'
  typeParams <- many1 parseTypeParameter
  char '>'
  return typeParams

parseTypeParameter = do
  identifier <- parseIdentifier
  char ':'
  classBound <- parseReferenceTypeSignature
  interfaceBounds <- many (char ':' >> parseReferenceTypeSignature)
  let interfaceBounds' = fmap mapInterfaceBoundRefType interfaceBounds
  let bound = case classBound of
        TypeCheckerClassRefType tccrtw ->
          TypeCheckerClassTypeTypeBound
            tccrtw
            (S.fromList interfaceBounds')
        TypeCheckerTypeVariableRefType sn -> TypeCheckerTypeVariableTypeBound sn
        TypeCheckerArrayRefType jts -> undefined
  return $ TypeCheckerTypeParameter identifier (Just bound)

mapInterfaceBoundRefType :: TypeCheckerReferenceTypeWrapper -> TypeCheckerClassReferenceTypeWrapper
mapInterfaceBoundRefType (TypeCheckerClassRefType tccrtw) = tccrtw
mapInterfaceBoundRefType _ = undefined

parseIdentifier = do
  fc  <- oneOf firstChar
  r   <- optionMaybe (many $ oneOf rest)
  spaces
  return $ case r of
           Nothing -> constructSimpleName (T.pack [fc])
           Just s  -> constructSimpleName (T.pack (fc : s))
  where firstChar = ['A'..'Z'] ++ ['a'..'z'] ++ "_"
        rest      = firstChar ++ ['0'..'9']

parseMethodSignature = do
  typeParams <- optionMaybe parseTypeParameters
  char '('
  refTypeSig <- manyTill (PrimitiveJavaTypeSignature <$> parsePrimitiveType <|> ReferenceJavaTypeSignature <$> parseReferenceTypeSignature) (char ')')
  result <- (PrimitiveJavaTypeSignature <$> (char 'V' >> pure V)) <|>
    (PrimitiveJavaTypeSignature <$> parsePrimitiveType) <|>
    (ReferenceJavaTypeSignature <$> parseReferenceTypeSignature)
  let tps = fromMaybe [] typeParams
  return (tps,refTypeSig,result)

isClassPathTypeBoolean :: ClassPathType -> Bool
isClassPathTypeBoolean Z = True
isClassPathTypeBoolean _ = False

isClassPathTypeInteger :: ClassPathType -> Bool
isClassPathTypeInteger I = True
isClassPathTypeInteger _ = False

getClassPathTypeReference :: ClassPathType -> Maybe TypeCheckerClassReferenceTypeWrapper
getClassPathTypeReference (L cpcrt) = Just cpcrt
getClassPathTypeReference _ = Nothing

getClassPathTypeVariable :: ClassPathType -> Maybe SimpleName
getClassPathTypeVariable (T sn) = Just sn
getClassPathTypeVariable _ = Nothing

getClassFieldType :: ClassDescriptor -> T.Text -> Maybe ClassPathType
getClassFieldType ClassDescriptor {..} fieldName =
  (\Field {..} -> ftype) <$> Data.List.find (\Field {..} -> fname == fieldName) fields

magicByteString :: [Word8]
magicByteString = B.unpack (toLazyByteString (word32BE 0xCAFEBABE))

sep = T.pack "/"

instance FS.Enum ClassAccessFlag where
  fromEnum CPublic = FS.maskValue (FS.Mask (bit 0)) (FS.Value (bit 0))
  fromEnum CInterface = FS.maskValue (FS.Mask (bit 9)) (FS.Value (bit 9))
  fromEnum CAbstract = FS.maskValue (FS.Mask (bit 10))  (FS.Value (bit 10))

cInterfaceMaskedValue = FS.maskValue (FS.Mask (bit 9)) (FS.Value (bit 9)) :: FS.MaskedValue Word16 ClassAccessFlag
cAbstractMaskedValue = FS.maskValue (FS.Mask (bit 10))  (FS.Value (bit 10)) :: FS.MaskedValue Word16 ClassAccessFlag
cPublicMaskedValue = FS.maskValue (FS.Mask (bit 0))  (FS.Value (bit 0)) :: FS.MaskedValue Word16 ClassAccessFlag

instance FS.Enum FieldAccessFlag where
  fromEnum FStatic = FS.maskValue (FS.Mask (bit 3)) (FS.Value (bit 3))

fStaticMaskedValue = FS.maskValue (FS.Mask (bit 3)) (FS.Value (bit 3)) :: FS.MaskedValue Word16 FieldAccessFlag

instance FS.Enum MethodAccessFlag where
  fromEnum MStatic = FS.maskValue (FS.Mask (bit 3)) (FS.Value (bit 3))
  fromEnum MAbstract = FS.maskValue (FS.Mask (bit 10)) (FS.Value (bit 10))
  fromEnum MSynthetic = FS.maskValue (FS.Mask (bit 12)) (FS.Value (bit 12))
  fromEnum MBridge = FS.maskValue (FS.Mask (bit 6)) (FS.Value (bit 6))

mStaticMaskedValue = FS.maskValue (FS.Mask (bit 3)) (FS.Value (bit 3)) :: FS.MaskedValue Word16 MethodAccessFlag
mAbstractMaskedValue = FS.maskValue (FS.Mask (bit 10))  (FS.Value (bit 10)) :: FS.MaskedValue Word16 MethodAccessFlag
mSyncheticMaskedValue = FS.maskValue (FS.Mask (bit 12))  (FS.Value (bit 12)) :: FS.MaskedValue Word16 MethodAccessFlag
mBridgeMaskedValue = FS.maskValue (FS.Mask (bit 6))  (FS.Value (bit 6)) :: FS.MaskedValue Word16 MethodAccessFlag

instance Show (FS.T w a) where
  show FS.Cons{..} = "Nothing"

instance Show ClassDescriptor where
  show ClassDescriptor {..} = abs++"class "++show name++showClassTypeParameters typeParameters++" extends "++show parent++
                              (if not (null interfaceClasses)
                                then " implements "++Data.List.intercalate "," (S.toList (S.map show interfaceClasses))
                                else "")++"\n"++
                              "Fields:\n"++concat (foldl (\l f -> ("         "++show f++"\n"):l) [] fields)++"\n"++
                              "Methods:\n"++concat (foldl (\l m -> ("          "++show m++"\n"):l) [] methods)++"\n"++
                              "Signature: "++foldl (\l tp -> show tp++",") "" typeParameters
                              where
                                abs = if FS.match accessFlags cAbstractMaskedValue then "abstract " else ""
                                showClassTypeParameters tps = "<"++params++">"
                                  where params = intercalate "," (V.toList (V.map show tps))

instance Show Field where
  show Field {..} = show ftype++" "++T.unpack fname

instance Show Method where
  show Method {..} = T.unpack mname++" "++T.unpack mdescriptor
    where
      abs = if FS.match maccessFlags mAbstractMaskedValue  then "abstract " else ""

readClassFile :: ClassReference -> T.Text -> IO (Maybe ClassFile)
readClassFile classRef fp =
  E.catch
    (readClassFile' classRef fp)
    (\e -> do
      let err = E.displayException (e :: E.IOException)
      hPutStrLn stderr ("failure accessing class file in classpath "++err)
      exitWith (ExitFailure 1))

readClassFile' :: ClassReference -> T.Text -> IO (Maybe ClassFile)
readClassFile' (DirectoryReference directory) name = do
  let fp = directory <> sep <> name <> T.pack ".class"
  withBinaryFile (T.unpack fp) ReadMode (readClassFile'' (T.unpack fp))
readClassFile' (JarReference jar) name =
  return Nothing

readClassFile'' :: FilePath -> Handle -> IO (Maybe ClassFile)
readClassFile'' fp handle = do
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
    interfaces <- V.replicateM interfaces_count (getIndex handle)
    fields_count <- getCount handle
    fields <- V.replicateM fields_count (readFieldInfo handle)
    methods_count <- getCount handle
    methods <- V.replicateM methods_count (readMethodInfo handle)
    attributes_count <- getCount handle
    attributes <- V.replicateM attributes_count (readAttributeInfo handle)

    return $ Just (ClassFile { minor_version=decode minor :: Word16
                             , major_version=decode major :: Word16
                             , constant_pool=cp
                             , access_flags=access_flags
                             , this_class=this_class
                             , super_class=super_class
                             , interfaces=interfaces
                             , fields_info=fields
                             , methods_info=methods
                             , attributes_info=attributes
                             })
  else
    return Nothing

{-- This function requires the state monad because long and double constants consume 2 slots in the constant pool Vector -}
readConstantPoolInfo :: Handle -> ST.StateT Bool IO Cp_info
readConstantPoolInfo handle = do
  isRepeat <- ST.get
  if isRepeat then do
    ST.put False
    return CpEmpty
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
      15 -> fmap MethodHandleInfo (readMethodHandleInfo handle)
      16 -> fmap MethodTypeInfo (readMethodTypeInfo handle)
      17 -> fmap DynamicInfo (readDynamicInfo handle)
      18 -> fmap InvokeDynamicInfo (readInvokeDynamicInfo handle)
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

readMethodHandleInfo :: Handle -> IO CONSTANT_MethodHandle_info
readMethodHandleInfo handle = do
  byte <- B.hGet handle 1
  let mh_reference_kind = (decode byte :: Word8)
  mh_reference_index <- getIndex handle
  return $ CONSTANT_MethodHandle_info {..}

readMethodTypeInfo :: Handle -> IO CONSTANT_MethodType_info
readMethodTypeInfo handle = do
  mt_descriptor_index <- getIndex handle
  return $ CONSTANT_MethodType_info {..}

readDynamicInfo :: Handle -> IO CONSTANT_Dynamic_info
readDynamicInfo handle = do
  d_bootstrap_method_attr_index <- getIndex handle
  d_name_and_type_index <- getIndex handle
  return $ CONSTANT_Dynamic_info {..}

readInvokeDynamicInfo :: Handle -> IO CONSTANT_InvokeDynamic_info
readInvokeDynamicInfo handle = do
  id_bootstrap_method_attr_index <- getIndex handle
  id_name_and_type_index <- getIndex handle
  return $ CONSTANT_InvokeDynamic_info {..}

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
  attribute_bytes <- B.hGet handle attributeLength
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

getSignature :: ClassFile -> Vector Attribute_info -> Maybe T.Text
getSignature cf attributes =
  case getAttributeByName cf attributes (T.pack "Signature") of
    Nothing -> Nothing
    Just Attribute_info {..} -> Just $ getUtf8FromConstantPool cf (fromIntegral (decode attribute_bytes :: Word16) :: Int)

getAttributeByName :: ClassFile -> Vector Attribute_info -> T.Text -> Maybe Attribute_info
getAttributeByName cf attributes name =
  let filteredVector = V.filter (\Attribute_info {..} -> getUtf8FromConstantPool cf attribute_name_index == name) attributes
  in
    filteredVector V.!? 0

getClassFromConstantPool :: ClassFile -> Int -> CONSTANT_Class_info
getClassFromConstantPool ClassFile {constant_pool=cp} index =
  let (ClassInfo c) = cp V.! (index - 1) in c

getUtf8FromConstantPool :: ClassFile -> Int -> T.Text
getUtf8FromConstantPool ClassFile {constant_pool=cp} index =
  let cpInfo = cp V.! (index - 1)
  in
    case cpInfo of
      (Utf8Info u) -> u_text u
      _ -> trace (show index++":"++show cpInfo) undefined

createClassDescriptor :: ClassFile -> ClassDescriptor
createClassDescriptor classFile@ClassFile {..} =
  let classInfo = getClassFromConstantPool classFile this_class
      accessFlags = FS.Cons access_flags
      name = classPathValidTypeName (constructQualifiedName $ getUtf8FromConstantPool classFile (ci_name_index classInfo))
      maybeClassSignatureText = getSignature classFile attributes_info
      {--!x = trace (show $ runParser parseClassSignature () "" . T.unpack <$> maybeClassSignatureText) 1--}
      maybeClassSignature = E.fromRight undefined . runParser parseClassSignature () "" . T.unpack <$> maybeClassSignatureText
      typeParameters = case maybeClassSignature of
        Nothing -> V.empty
        Just (typeParams,_,_) -> maybe V.empty V.fromList typeParams

      parent = case maybeClassSignature of
        Nothing -> if super_class > 0
                    then
                      TypeCheckerClassReferenceTypeWrapper
                        (classPathValidTypeName $
                          constructQualifiedName $
                            getUtf8FromConstantPool classFile (ci_name_index (getClassFromConstantPool classFile super_class)))
                        Nothing
                    else
                      TypeCheckerClassReferenceTypeWrapper
                        (classPathValidTypeName
                          createQNameObject)
                          Nothing -- Only java/lang/Object should get here 
        Just (_, parentClassReferenceType, _) -> parentClassReferenceType

      interfaceClasses = case maybeClassSignature of
        Nothing ->  S.fromList $ fmap (
                      (\qn -> TypeCheckerClassReferenceTypeWrapper (classPathValidTypeName qn) Nothing)
                        . constructQualifiedName
                          . getUtf8FromConstantPool classFile
                            . ci_name_index . getClassFromConstantPool classFile)
                        (V.toList interfaces)
        Just (_, _, interfaceClassReferenceTypeList) -> S.fromList interfaceClassReferenceTypeList
      fields = foldl' (\list f -> mapField classFile f:list) [] fields_info
      methods = foldl' (\list m -> mapMethod classFile m:list) [] methods_info
      parentTypeParams = Map.empty --maybe Map.empty snd maybeParseResult

      mapField :: ClassFile -> Field_info -> Field
      mapField classFile fi =
        let fname = getUtf8FromConstantPool classFile (fi_name_index fi)
            faccessFlags = FS.Cons $ fi_access_flags fi
            maybeFieldSignatureText = getSignature classFile (fi_attributes_info fi)
            maybeFieldSignature = E.fromRight undefined . runParser parseReferenceTypeSignature () "" . T.unpack <$> maybeFieldSignatureText
            ftype = case maybeFieldSignature of
              Nothing -> readType $ getUtf8FromConstantPool classFile (fi_descriptor_index fi)
              Just rts -> mapClassPathReferenceTypeToClassPathType rts
            fclassTypeParameters = typeParameters
            fcClassName = name
        in
          Field {..}

      mapMethod :: ClassFile -> Method_info -> Method
      mapMethod classFile mi =
        let mname = getUtf8FromConstantPool classFile (mi_name_index mi)
            maccessFlags = FS.Cons $ mi_access_flags mi
            maybeMethodSignatureText = getSignature classFile (mi_attributes_info mi)
            mdescriptor = case maybeMethodSignatureText of
              Nothing -> getUtf8FromConstantPool classFile (mi_descriptor_index mi)
              Just methodSig -> methodSig
            mclassTypeParameters = typeParameters
            mcClassName = name
        in
          Method {..}

  in
    ClassDescriptor {..}

getClass :: T.Text -> StateT ClassPath IO (Maybe ClassDescriptor)
getClass qualifiedName = do
  cp@ClassPath {..} <- get
  let maybeClass = classMap Map.!? qualifiedName
  case maybeClass of
    Just clazz -> return (Just clazz)
    Nothing -> do
      let (package,clazz) = T.breakOnEnd sep qualifiedName
      let maybePackage = referenceMap Map.!? package
      let maybeRef = maybePackage >>= (Map.!? clazz)
      case maybeRef of
        Nothing -> return Nothing
        Just ref -> do
          maybeClassFile <- lift $ readClassFile ref qualifiedName
          case maybeClassFile of
            Nothing -> return Nothing
            Just classFile -> do
              let newClassDescriptor = createClassDescriptor classFile
              put ClassPath {classMap=Map.insert qualifiedName newClassDescriptor classMap,..}
              return $ Just newClassDescriptor

getClassPathValidType :: TypeCheckerValidTypeQualifiedNameWrapper -> StateT ClassPath IO ClassDescriptor
getClassPathValidType vtqnw = do
  maybeClassDesciptor <- getClass (showt (getValidTypeQName vtqnw))
  case maybeClassDesciptor of
    Nothing -> error ("Classpath consitency error. Unable to load class: "++show (getValidTypeQName vtqnw))
    Just cd -> return cd

hasClass :: ClassPath -> QualifiedName -> Bool
hasClass cp qualifiedName =
  case getClassPathClassType cp qualifiedName of Just _ -> True; Nothing -> False

getClassPathClassType :: ClassPath -> QualifiedName -> Maybe TypeCheckerValidTypeQualifiedNameWrapper
getClassPathClassType cp qualifiedName =
  let (package,clazz) = T.breakOnEnd sep (toText (showb qualifiedName))
      maybeSubMap = if T.length package > 0 then referenceMap cp Map.!? package else Nothing
      maybeRef = (Map.!? clazz) =<< maybeSubMap
  in
    case maybeRef of
      Just _ -> Just (classPathValidTypeName qualifiedName)
      Nothing -> Nothing

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
refMapFromDirectory fp =
  E.catch
    (refMapFromDirectory' fp)
    (\e -> do
      let err = E.displayException (e :: E.IOException)
      hPutStrLn stderr ("failure accessing classpath directory "++err)
      exitWith (ExitFailure 1))

refMapFromDirectory' :: FilePath -> IO PackageMap
refMapFromDirectory' directoryPath = do
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
