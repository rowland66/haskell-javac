module ConstantPoolBuilder
  ( ConstantPool
  , ConstantPoolST
  , newConstantPool
  , getCount
  , toBytes
  , addUtf8
  , addClass
  , addFieldRef
  , addMethodRef
  , addMethodRef'
  , addInteger
  , addString
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.ByteString.Lazy as B
import Control.Monad.Trans.State
import Data.Functor.Identity
import Data.ByteString.Builder
import Data.Word
import Data.Bits (shiftL,(.|.))
import Debug.Trace
import qualified Parser as P
import qualified Parser2 as P2
import Data.Int (Int32)
import TypeInfo (Type)

data ConstantPool = ConstantPool { pool :: [B.ByteString]
                                 , size :: Word16
                                 , utf8Map :: Map.Map String Word16
                                 , classMap :: Map.Map P.QualifiedName Word16
                                 , fieldRefMap :: Map.Map String Word16
                                 , methodRefMap :: Map.Map String Word16
                                 , nameAndTypeMap :: Map.Map Word32 Word16
                                 , stringMap :: Map.Map String Word16
                                 }

type ConstantPoolST = StateT ConstantPool Identity

newConstantPool :: ConstantPool
newConstantPool =
  ConstantPool { pool=[]
               , size=0
               , utf8Map = Map.empty
               , classMap = Map.empty
               , fieldRefMap = Map.empty
               , methodRefMap = Map.empty
               , nameAndTypeMap = Map.empty
               , stringMap = Map.empty
               }

getCount :: ConstantPool -> Word16
getCount ConstantPool{size=s} = s+1

toBytes :: ConstantPool -> B.ByteString
toBytes ConstantPool{pool=p} =
  foldl (flip mappend) B.empty p

addUtf8 :: String -> ConstantPoolST Word16
addUtf8 str = do
  cp@ConstantPool{pool=p,size=s,utf8Map=umap} <- get
  if Map.member str umap then
    return (umap Map.! str)
  else do
    put $ cp {pool=createUtf8ByteString str:p, size=s+1, utf8Map=Map.insert str (s+1) umap}
    return (s+1)

addClass :: P.QualifiedName -> ConstantPoolST Word16
addClass name = do
  ConstantPool{classMap=cmap} <- get
  if Map.member name cmap then
    return (cmap Map.! name)
  else do
    classNameStringNdx <- addUtf8 (show name)
    modify (\cp@ConstantPool{pool=p,size=s} ->
      cp {pool=createClassByteString classNameStringNdx:p, size=s+1, classMap=Map.insert name (s+1) cmap})
    fmap (\ConstantPool{size=s} -> s) get

addFieldRef :: P.QualifiedName -> P.SimpleName -> Type -> ConstantPoolST Word16
addFieldRef className name tp = do
  ConstantPool{fieldRefMap=frmap} <- get
  let key = show className++":"++show name
  if Map.member key frmap then
    return (frmap Map.! key)
  else do
    let descriptor = show tp
    classNdx <- addClass className
    nameAndTypeNdx <- addNameAndType (show name) descriptor
    modify (\cp@ConstantPool{pool=p,size=s} ->
      cp {pool=createFieldRefByteString classNdx nameAndTypeNdx:p, size=s+1, fieldRefMap=Map.insert key (s+1) frmap})
    fmap (\ConstantPool{size=s} -> s) get

addMethodRef :: P.QualifiedName -> P.SimpleName -> [Type] -> String -> ConstantPoolST Word16
addMethodRef className name params tp = do
  let key = show className++":"++show name++":"++foldr (\p ps -> show p++ps) [] params
  let descriptor = "("++foldr (\p d -> show p++d) "" params++")"++tp
  addMethodRef' className name descriptor key

addMethodRef' :: P.QualifiedName -> P.SimpleName -> String -> String -> ConstantPoolST Word16
addMethodRef' className name descriptor mapKey = do
  ConstantPool{methodRefMap=mrmap} <- get
  if Map.member mapKey mrmap then
    return (mrmap Map.! mapKey)
  else do
    classNdx <- addClass className
    nameAndTypeNdx <- addNameAndType (show name) descriptor
    modify (\cp@ConstantPool{pool=p,size=s} ->
      cp {pool=createMethodRefByteString classNdx nameAndTypeNdx:p, size=s+1, methodRefMap=Map.insert mapKey (s+1) mrmap})
    fmap (\ConstantPool{size=s} -> s) get

addNameAndType :: String -> String -> ConstantPoolST Word16
addNameAndType name descriptor = do
  cp@ConstantPool{nameAndTypeMap=natmap} <- get
  nameNdx <- addUtf8 name
  typeNdx <- addUtf8 descriptor
  let key = shiftL (fromIntegral nameNdx :: Word32) 16 .|. (fromIntegral typeNdx :: Word32)
  if Map.member key natmap then
    return (natmap Map.! key)
  else do
    modify (\cp@ConstantPool{pool=p, size=s} ->
      cp {pool=createNameAndTypeByteString nameNdx typeNdx:p, size=s+1, nameAndTypeMap=Map.insert key (s+1) natmap})
    fmap (\ConstantPool{size=s} -> s) get

addInteger :: Int32 -> ConstantPoolST Word16
addInteger v = do
  modify (\cp@ConstantPool{pool=p, size=s} ->
    cp {pool=createIntegerByteString (fromIntegral v :: Word32):p, size=s+1})
  fmap (\ConstantPool{size=s} -> s) get

addString :: String -> ConstantPoolST Word16
addString str = do
  cp@ConstantPool{stringMap=stringMap} <- get
  if Map.member str stringMap then
    return (stringMap Map.! str)
  else do
    utf8Ndx <- addUtf8 str
    let newString = createStringByteString utf8Ndx
    modify (\cp@ConstantPool{pool=p, size=s} ->
      cp {pool=newString:p, size=s+1, stringMap=Map.insert str (s+1) stringMap})
    fmap (\ConstantPool{size=s} -> s) get

createUtf8ByteString :: String -> B.ByteString
createUtf8ByteString str = toLazyByteString (mappend (word8 0x01) (mappend (word16BE (fromIntegral (length str) :: Word16)) (string7 str)))

createClassByteString :: Word16 ->  B.ByteString
createClassByteString nameNdx = toLazyByteString (mappend (word8 0x07) (word16BE nameNdx))

createFieldRefByteString :: Word16 -> Word16 -> B.ByteString
createFieldRefByteString classNdx natNdx = toLazyByteString (mappend (word8 0x09) (mappend (word16BE classNdx) (word16BE natNdx)))

createMethodRefByteString :: Word16 -> Word16 -> B.ByteString
createMethodRefByteString classNdx natNdx = toLazyByteString (mappend (word8 0x0A) (mappend (word16BE classNdx) (word16BE natNdx)))

createNameAndTypeByteString :: Word16 -> Word16 -> B.ByteString
createNameAndTypeByteString nameNdx typeNdx = toLazyByteString (mappend (word8 0x0C) (mappend (word16BE nameNdx) (word16BE typeNdx)))

createIntegerByteString :: Word32 -> B.ByteString
createIntegerByteString value = toLazyByteString (mappend (word8 0x03) (word32BE value))

createStringByteString :: Word16 -> B.ByteString
createStringByteString constantNdx = toLazyByteString (mappend (word8 0x08) (word16BE constantNdx))