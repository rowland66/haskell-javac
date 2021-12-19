{-# LANGUAGE RecordWildCards #-}

module ByteCodeBuilder
  ( ClassByteCode
  , buildClass
  ) where

import qualified Data.ByteString.Lazy as B
import Data.ByteString.Builder
import Control.Monad.Trans.State
import Control.Monad (foldM)
import Data.Int
import Data.Word
import Data.List

import ConstantPoolBuilder
import Parser2
import qualified Parser as P
import TypeChecker
import Debug.Trace

data ClassByteCode = ClassByteCode { accessFlags :: Word16
                                   , classNdx :: Word16
                                   , superNdx :: Word16
                                   , fields :: [B.ByteString]
                                   , methods :: [B.ByteString]
                                   }

buildClass :: TypedClazz -> B.ByteString
buildClass clazz =
  let (ClassByteCode {..}, cp) = runState (buildClass' clazz) newConstantPool in
  B.concat $ classHeader :
    (toLazyByteString (word16BE (getCount cp))) :
    (toBytes cp) :
    (toLazyByteString (word16BE accessFlags)) :
    (toLazyByteString (word16BE classNdx)) :
    (toLazyByteString (word16BE superNdx)) :
    (toLazyByteString (word16BE 0x0000)) :
    (toLazyByteString (word16BE (fromIntegral (length fields) :: Word16))) :
    (B.concat fields) :
    (toLazyByteString (word16BE (fromIntegral (length methods) :: Word16))) :
    (B.concat methods) :
    (toLazyByteString (word16BE 0x0000)) :
    []

buildClass' :: TypedClazz -> ConstantPoolST ClassByteCode
buildClass' clazz@(NewTypedClazz name extends fields constructors methods) = do
  clazzNdx <- addClass name
  let parentCls = case extends of NewExtends _ parent -> parent; ExtendsObject -> P.createQNameObject
  parentNdx <- addClass parentCls
  fieldsInfo <- sequence $ fmap (\f -> buildFieldInfo f) fields
  constructorsMethodInfo <- sequence $ fmap (\m -> buildConstructorMethodInfo parentCls m) constructors
  methodsInfo <- sequence $ fmap (\m -> buildMethodInfo m) methods
  return $ ClassByteCode {accessFlags=0x0001, classNdx=clazzNdx, superNdx=parentNdx, fields=fieldsInfo, methods=(constructorsMethodInfo ++ methodsInfo)}

classHeader :: B.ByteString
classHeader = toLazyByteString (word32BE 0xCAFEBABE <> word16BE 0x0000 <> word16BE 0x0037)

buildFieldInfo :: Field -> ConstantPoolST B.ByteString
buildFieldInfo (NewField _ tp _ name) = do
  nameNdx <- addUtf8 (show name)
  descriptorNdx <- addUtf8 ("L"++(show tp)++";")
  return $ toLazyByteString ((word16BE 0x0001) <> (word16BE nameNdx) <> (word16BE descriptorNdx) <> (word16BE 0x0000))

buildMethodInfo :: TypedMethod -> ConstantPoolST B.ByteString
buildMethodInfo method@(NewTypedMethod name params tp _) = do
  let descriptor = "("++(foldr (\(NewParameter _ ptype _) d -> ("L"++(show ptype)++";")++d) "" params)++")"++"L"++(show tp)++";"
  nameNdx <- addUtf8 (show name)
  descriptorNdx <- addUtf8 descriptor
  codeAttrInfo <- buildMethodCodeAttrInfo method
  return $ toLazyByteString ((word16BE 0x0001) <> (word16BE nameNdx) <> (word16BE descriptorNdx) <> (word16BE 0x0001) <> (lazyByteString codeAttrInfo))

buildConstructorMethodInfo :: P.QualifiedName -> TypedConstructor -> ConstantPoolST B.ByteString
buildConstructorMethodInfo parentCls constructor@(NewTypedConstructor params superInvocation assignments) = do
  let descriptor = "("++(foldr (\(NewParameter _ ptype _) d -> ("L"++(show ptype)++";")++d) "" params)++")"++"V"
  nameNdx <- addUtf8 (show P.createNameInit)
  descriptorNdx <- addUtf8 descriptor
  codeAttributeInfo <- (buildConstructorCodeAttrInfo (fromIntegral (length params) :: Word16) parentCls superInvocation assignments)
  return $ toLazyByteString (
    (word16BE 0x0001) <>
    (word16BE nameNdx) <>
    (word16BE descriptorNdx) <>
    (word16BE 0x0001) <>
    (lazyByteString codeAttributeInfo))

buildMethodCodeAttrInfo :: TypedMethod -> ConstantPoolST B.ByteString
buildMethodCodeAttrInfo (NewTypedMethod _ params _ term) = do
  (codeBytes, maxStack) <- generateTermCode term
  buildCodeAttrInfo maxStack (fromIntegral (length params) :: Word16) (toLazyByteString ((lazyByteString codeBytes) <> (word8 0xb0)))

buildConstructorCodeAttrInfo :: Word16 -> P.QualifiedName -> TypedConstructorInvocation -> [TypedAssignment] -> ConstantPoolST B.ByteString
buildConstructorCodeAttrInfo paramsCount parentCls (NewTypedConstructorInvocation superTerms) assignments = do
  (superInvocationCodeBytes, superInvocationMaxStack) <- generateSuperInvocation parentCls superTerms
  (assignmentCodeBytesList, assignmentMaxStack) <- foldM (\(list,ms) a -> (fmap (\(c, ms') -> (c:list, (max ms ms'))) (generateAssignmentCode a))) ([],0) assignments
  let codeBytes = B.concat $ superInvocationCodeBytes : (reverse assignmentCodeBytesList)
  buildCodeAttrInfo (max superInvocationMaxStack assignmentMaxStack) paramsCount (toLazyByteString ((lazyByteString codeBytes) <> (word8 0xb1)))

buildCodeAttrInfo :: Word16 -> Word16 -> B.ByteString -> ConstantPoolST B.ByteString
buildCodeAttrInfo maxStack paramsCount codeBytes = do
  nameNdx <- addUtf8 "Code"
  let codeBytesLength = (fromIntegral (B.length codeBytes) :: Word32)
  let codeAttributeInfoLength = codeBytesLength + 12
  return $ toLazyByteString (
    (word16BE nameNdx) <>
    (word32BE codeAttributeInfoLength) <>
    (word16BE maxStack) <>
    (word16BE (paramsCount+1)) <>
    (word32BE codeBytesLength) <>
    (lazyByteString codeBytes) <>
    (word16BE 0x0000) <> {-- Exception table length -}
    (word16BE 0x0000))   {-- Attributes table length -}

generateAssignmentCode :: TypedAssignment -> ConstantPoolST (B.ByteString, Word16)
generateAssignmentCode (NewTypedAssignment lhTerm rhTerm) = generateAssignmentCode' lhTerm rhTerm

generateAssignmentCode' :: TypedTerm -> TypedTerm -> ConstantPoolST (B.ByteString, Word16)
generateAssignmentCode' (TypedApplication t (TypedFieldAccess {fName=field, fTyp=tp})) rhTerm= do
  (lhByteCode, lhMaxStack) <- generateTermCode t
  (rhByteCode, rhMaxStack) <- generateTermCode rhTerm
  fieldRef <- (addFieldRef (getTypedTermType t) field tp)
  let byteCode = toLazyByteString $ (lazyByteString lhByteCode) <> (lazyByteString rhByteCode) <> (word8 0xb5) <> (word16BE fieldRef)
  return (byteCode, (max lhMaxStack (rhMaxStack+1)))

generateTermCode :: TypedTerm -> ConstantPoolST (B.ByteString, Word16)
generateTermCode term = do
  (expressionByteCode, maxStack) <- generateTermCode' term
  return $ (toLazyByteString (lazyByteString expressionByteCode), maxStack)

generateTermCode' :: TypedTerm -> ConstantPoolST (B.ByteString, Word16)
generateTermCode' (TypedValue (TypedVariable {vPosition=p})) = do
  return $ ((generateLoadReference p), 1)
generateTermCode' (TypedValue (TypedObjectCreation {ocTyp=tp, ocTerms=terms})) = do
  classNdx <- addClass tp
  (constructorTerms, maxStack) <- (generateTermListCode terms)
  constructorMethodRef <- (addMethodRef tp P.createNameInit (fmap getTypedTermType terms) "V")
  let byteCode = toLazyByteString (
                   (word8 0xbb) <> (word16BE classNdx) <>
                   (word8 0x59) <>
                   (lazyByteString constructorTerms) <>
                   (word8 0xb7) <>
                   (word16BE constructorMethodRef))
  return (byteCode, maxStack+2) {--Add 2 for the new object ref and the duplicate -}
generateTermCode' (TypedValue (TypedCast {cTyp=tp, cTerm=term})) = do
  classNdx <- addClass tp
  (castTermByteCode, maxStack) <- generateTermCode' term
  let byteCode = toLazyByteString ((lazyByteString castTermByteCode) <> (word8 0xc0) <> (word16BE classNdx))
  return (byteCode, maxStack)
generateTermCode' (TypedApplication term (TypedFieldAccess {fName=name, fTyp=tp})) = do
  (applicationTermByteCode, maxStack) <- generateTermCode' term
  fieldRef <- (addFieldRef (getTypedTermType term) name tp)
  let byteCode = toLazyByteString ((lazyByteString applicationTermByteCode) <> (word8 0xb4) <> (word16BE fieldRef))
  return (byteCode, maxStack)
generateTermCode' (TypedApplication term (TypedMethodInvocation {mName=name, mTyp=tp, mTerms=terms})) = do
  (methodInvocationTermByteCode, termMaxStack) <- generateTermCode' term
  (methodInvocationTerms, argumentListMaxStack) <- (generateTermListCode terms)
  methodRef <- (addMethodRef (getTypedTermType term) name (fmap getTypedTermType terms) (show tp))
  let byteCode = toLazyByteString ((lazyByteString methodInvocationTermByteCode) <>
                   (lazyByteString methodInvocationTerms) <>
                   (word8 0xb6) <>
                   (word16BE methodRef))
  return (byteCode, (max termMaxStack (argumentListMaxStack+1)))

generateTermListCode :: [TypedTerm] -> ConstantPoolST (B.ByteString, Word16)
generateTermListCode terms = generateTermListCode' mempty 0 0 terms

{--We use to Word16 values to track the maximum stack required to evaluate the term list. As we move through the
   list, we add a value to the startStack because every term on the list leaves a value on the stack. We also track
   the maximum stack required to evaluate each term plus the increasing with each term startStack. -}
generateTermListCode' :: Builder -> Word16 -> Word16 -> [TypedTerm] -> ConstantPoolST (B.ByteString, Word16)
generateTermListCode' b startStack maxStack [] = return ((toLazyByteString b), maxStack)
generateTermListCode' b startStack maxStack (t:ts) = do
  (termByteCode, maxStack') <- generateTermCode' t
  generateTermListCode' (b <> (lazyByteString termByteCode)) (startStack+1) (max maxStack (maxStack' + startStack)) ts

generateSuperInvocation :: P.QualifiedName -> [TypedTerm] -> ConstantPoolST (B.ByteString, Word16)
generateSuperInvocation parentCls terms = do
  (invocationTerms, maxStack) <- (generateTermListCode terms)
  methodRef <- addMethodRef parentCls P.createNameInit (fmap getTypedTermType terms) "V"
  let byteCode = toLazyByteString (
                   (word8 0x2a) <>
                   (lazyByteString invocationTerms) <>
                   (word8 0xb7) <> (word16BE methodRef))
  return (byteCode, maxStack+1)

generateLoadReference :: Word8 -> B.ByteString
generateLoadReference 0 = toLazyByteString (word8 0x2a)
generateLoadReference 1 = toLazyByteString (word8 0x2b)
generateLoadReference 2 = toLazyByteString (word8 0x2c)
generateLoadReference 3 = toLazyByteString (word8 0x2d)
generateLoadReference p = toLazyByteString ((word8 0x19) <> (word8 p))
