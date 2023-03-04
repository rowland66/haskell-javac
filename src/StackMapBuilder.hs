{-# LANGUAGE RecordWildCards #-}

module StackMapBuilder
( StackMapFrame
, StackMapFrameWithOffset(..)
, startingStackFrame
, addStackMapFrame
, createStackMapFrameByteString
, createStackTableAttribute
) where

import qualified Data.ByteString.Lazy as B
import Data.ByteString.Builder (Builder, toLazyByteString, word32BE, word16BE, word8, lazyByteString)
import Control.Monad ( foldM )
import Data.Int (Int64)
import qualified Parser as P
import qualified Parser2 as P2
import TypeInfo(Type(..),convertTypeCheckerJavaType)
import TypeValidator
import TypeCheckerTypes
import ConstantPoolBuilder ( ConstantPoolST, addClass, addUtf8 )

data StackMapFrame = StackMapFrame { locals :: [Type], stack :: [Type]} deriving Show

data StackMapFrameWithOffset = StackMapFrameWithOffset Int64 StackMapFrame

startingStackFrame :: Type -> [ValidTypeParameter] -> StackMapFrame
startingStackFrame className params =
  let paramTypes = fmap 
        (\ValidTypeParameter {..} -> convertTypeCheckerJavaType vpType)
        params
  in
    StackMapFrame { locals=className:paramTypes, stack=[] }

addStackMapFrame :: StackMapFrame -> [Type] -> StackMapFrame
addStackMapFrame StackMapFrame {..} newStack =
  let topFrame = stack
  in
    StackMapFrame {stack=newStack,..}

createStackTableAttribute :: [B.ByteString] -> ConstantPoolST B.ByteString
createStackTableAttribute [] = return B.empty
createStackTableAttribute stackFrameMapBytesList = do
  utf8Ndx <- addUtf8 "StackMapTable"
  let attributeLength = foldr (\bs acc -> acc + B.length bs) 0 stackFrameMapBytesList + 2
  let entries = foldr (\bs acc -> acc <> bs) B.empty stackFrameMapBytesList
  return $ toLazyByteString (  word16BE utf8Ndx
                            <> word32BE (fromIntegral attributeLength)
                            <> word16BE (fromIntegral (length stackFrameMapBytesList))
                            <> lazyByteString entries)

createStackMapFrameByteString :: StackMapFrameWithOffset -> ConstantPoolST B.ByteString
createStackMapFrameByteString (StackMapFrameWithOffset offset StackMapFrame {..}) = do
  localVariableInfoBytes <- foldM (\b tp -> (b <>) <$> mapTypeToVariableInfo tp) mempty locals
  stackInfoBytes <- foldM (\b tp -> (b <>) <$> mapTypeToVariableInfo tp) mempty (reverse stack)
  return $ toLazyByteString $ word8 0xFF
                           <> word16BE (fromIntegral offset)
                           <> word16BE (fromIntegral (length locals))
                           <> localVariableInfoBytes
                           <> word16BE (fromIntegral (length stack))
                           <> stackInfoBytes

mapTypeToVariableInfo :: Type -> ConstantPoolST Builder
mapTypeToVariableInfo tp = do
  case tp of
    I -> return integerVariableInfo
    Z -> return integerVariableInfo
    L (TypeCheckerClassReferenceTypeWrapper vtn _) -> objectVariableInfo (getValidTypeQName vtn)
    _ -> undefined

integerVariableInfo :: Builder
integerVariableInfo = word8 0x01

objectVariableInfo :: P.QualifiedName -> ConstantPoolST Builder
objectVariableInfo qn = do
  classNdx <- addClass qn
  return $ word8 0x07 <> word16BE classNdx