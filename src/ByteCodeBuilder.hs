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
import qualified Data.Text as T

import ConstantPoolBuilder
import Parser2
import qualified Parser as P
import TypeChecker
import Debug.Trace
import qualified TypeChecker as P2
import Parser (QualifiedName)

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
buildClass' clazz@(NewTypedClazz name extends fields methods) = do
  clazzNdx <- addClass name
  let parentCls = case extends of NewExtends _ parent -> parent; ExtendsObject -> P.createQNameObject
  parentNdx <- addClass parentCls
  fieldsInfo <- mapM buildFieldInfo fields
  methodsInfo <- mapM buildMethodInfo methods
  return $ ClassByteCode {accessFlags=0x0001, classNdx=clazzNdx, superNdx=parentNdx, fields=fieldsInfo, methods=methodsInfo}

classHeader :: B.ByteString
classHeader = toLazyByteString (word32BE 0xCAFEBABE <> word16BE 0x0000 <> word16BE 0x0037)

buildFieldInfo :: Field -> ConstantPoolST B.ByteString
buildFieldInfo (NewField _ tp _ name) = do
  nameNdx <- addUtf8 (show name)
  descriptorNdx <- addUtf8 ("L"++show tp++";")
  return $ toLazyByteString (word16BE 0x0001 <> word16BE nameNdx <> word16BE descriptorNdx <> word16BE 0x0000)

buildMethodInfo :: TypedMethod -> ConstantPoolST B.ByteString
buildMethodInfo method@(NewTypedMethod name params tp _) = do
  let rtrnType = if name == P.createNameInit then "V" else "L"++show tp++";"
  let descriptor = "("++foldr (\(NewParameter _ ptype _) d -> ("L"++show ptype++";")++d) "" params++")"++rtrnType
  nameNdx <- addUtf8 (show name)
  descriptorNdx <- addUtf8 descriptor
  codeAttrInfo <- buildMethodCodeAttrInfo method
  return $ toLazyByteString (word16BE 0x0001 <> word16BE nameNdx <> word16BE descriptorNdx <> word16BE 0x0001 <> lazyByteString codeAttrInfo)

buildMethodCodeAttrInfo :: TypedMethod -> ConstantPoolST B.ByteString
buildMethodCodeAttrInfo (NewTypedMethod _ params _ (TypedMethodImpl term)) = do
  (codeBytes, maxStack) <- generateTermCode term
  boxCodeBytes <- generateTermBoxingByteCode term
  buildCodeAttrInfo maxStack
    (fromIntegral (length params) :: Word16)
    (toLazyByteString (lazyByteString codeBytes <> lazyByteString boxCodeBytes <> word8 0xb0))
buildMethodCodeAttrInfo (NewTypedMethod _ params _ (TypedConstructorImpl (NewTypedConstructorInvocation cls targetTermTypes superTerms) assignments)) = do
  (superInvocationCodeBytes, superInvocationMaxStack) <- generateSuperInvocation cls (zip targetTermTypes superTerms)
  (assignmentCodeBytesList, assignmentMaxStack) <- foldM (\(list,ms) a -> fmap (\(c, ms') -> (c:list, max ms ms')) (generateAssignmentCode a)) ([],0) assignments
  let codeBytes = B.concat $ superInvocationCodeBytes : reverse assignmentCodeBytesList
  buildCodeAttrInfo (max superInvocationMaxStack assignmentMaxStack) 
    (fromIntegral (length params) :: Word16) 
    (toLazyByteString (lazyByteString codeBytes <> word8 0xb1))

buildCodeAttrInfo :: Word16 -> Word16 -> B.ByteString -> ConstantPoolST B.ByteString
buildCodeAttrInfo maxStack paramsCount codeBytes = do
  nameNdx <- addUtf8 "Code"
  let codeBytesLength = (fromIntegral (B.length codeBytes) :: Word32)
  let codeAttributeInfoLength = codeBytesLength + 12
  return $ toLazyByteString (
    word16BE nameNdx <>
    word32BE codeAttributeInfoLength <>
    word16BE maxStack <>
    word16BE (paramsCount+1) <>
    word32BE codeBytesLength <>
    lazyByteString codeBytes <>
    word16BE 0x0000 <> {-- Exception table length -}
    word16BE 0x0000)   {-- Attributes table length -}

generateAssignmentCode :: TypedAssignment -> ConstantPoolST (B.ByteString, Word16)
generateAssignmentCode (NewTypedAssignment lhTerm rhTerm) = generateAssignmentCode' lhTerm rhTerm

generateAssignmentCode' :: TypedTerm -> TypedTerm -> ConstantPoolST (B.ByteString, Word16)
generateAssignmentCode' (TypedApplication (TypedReferenceTerm termTypeName t) TypedFieldAccess {fName=field, fTyp=tp}) rhTerm= do
  (lhByteCode, lhMaxStack) <- generateTermCode t
  (rhByteCode, rhMaxStack) <- generateTermCode rhTerm
  fieldRef <- addFieldRef termTypeName field tp
  {--rhTermBoxingByteCode <- generateTermBoxingByteCode rhTerm-}
  let byteCode = toLazyByteString $ lazyByteString lhByteCode <> lazyByteString rhByteCode <> word8 0xb5 <> word16BE fieldRef
  return (byteCode, max lhMaxStack (rhMaxStack+1))
generateAssignmentCode' _ _ = undefined

generateTermCode :: TypedTerm -> ConstantPoolST (B.ByteString, Word16)
generateTermCode term = do
  (expressionByteCode, maxStack) <- generateTermCode' term
  return (toLazyByteString (lazyByteString expressionByteCode), maxStack)

generateTermCode' :: TypedTerm -> ConstantPoolST (B.ByteString, Word16)
generateTermCode' (TypedValue TypedVariable {vPosition=p}) =
  return (generateLoadReference p, 1)
generateTermCode' (TypedValue TypedTypeName {tnTyp=tp}) =
  return (B.empty, 0)
generateTermCode' (TypedValue TypedIntegerLiteral {iTyp=tp, iValue=value}) = do
  intNdx <- addInteger value
  methodRef <- addMethodRef' tp (P.constructSimpleName (T.pack "valueOf")) "(I)Ljava/lang/Integer;" "java/lang/Integer:valueOf(I)"
  let byteCode = toLazyByteString (
                   word8 0x13 <> word16BE intNdx <>  -- ldc_w Integer Constant
                   word8 0xb8 <> word16BE methodRef) -- invokestatic MethodRef
  return (byteCode, 1)
generateTermCode' (TypedValue TypedStringLiteral {sTyp=tp, sValue=value}) = do
  strNdx <- addString value
  let byteCode = toLazyByteString (
                   word8 0x13 <> word16BE strNdx) -- ldc_w String Constant
  return (byteCode, 1)
generateTermCode' (TypedValue TypedBooleanLiteral {bTyp=tp, bValue=value}) = do
  methodRef <- addMethodRef' tp (P.constructSimpleName (T.pack "valueOf")) "(Z)Ljava/lang/Boolean;" "java/lang/Boolean:valueOf(Z)"
  let byteCode = toLazyByteString (
                   (if value then word8 0x04 else word8 0x03) <> -- iconst_1 (true) or iconst_0 (false) 
                   word8 0xb8 <> word16BE methodRef)                           -- invokestatic MethodRef
  return (byteCode, 1)
generateTermCode' (TypedValue TypedObjectCreation {ocTyp=tp, ocParamTyps=targetParamTypes, ocTerms=terms}) = do
  classNdx <- addClass tp
  (constructorTerms, maxStack) <- generateTermListCode (zip targetParamTypes terms)
  constructorMethodRef <- addMethodRef tp P.createNameInit (fmap getTypedTermType terms) "V"
  let byteCode = toLazyByteString (
                   word8 0xbb <> word16BE classNdx <>
                   word8 0x59 <>
                   lazyByteString constructorTerms <>
                   word8 0xb7 <>
                   word16BE constructorMethodRef)
  return (byteCode, maxStack+2) {--Add 2 for the new object ref and the duplicate -}
generateTermCode' (TypedValue TypedCast {cTyp=tp, cTerm=term}) = do
  classNdx <- addClass tp
  (castTermByteCode, maxStack) <- generateTermCode' term
  let byteCode = toLazyByteString (lazyByteString castTermByteCode <> word8 0xc0 <> word16BE classNdx)
  return (byteCode, maxStack)
generateTermCode' (TypedApplication (TypedReferenceTerm termType term) TypedFieldAccess {fName=name, fTyp=tp}) = do
  (applicationTermByteCode, maxStack) <- generateTermCode' term
  fieldRef <- addFieldRef termType name tp
  let byteCode = toLazyByteString (lazyByteString applicationTermByteCode <> word8 0xb4 <> word16BE fieldRef)
  return (byteCode, maxStack)
generateTermCode' (TypedApplication (TypedReferenceTerm termType term) TypedMethodInvocation {..}) = do
  let isStatic = case term of (TypedValue (TypedTypeName _)) -> True; _ -> False
  (methodInvocationTermByteCode, termMaxStack) <- generateTermCode' term
  (methodInvocationTerms, argumentListMaxStack) <- generateTermListCode (zip mParamTyps mTerms)
  methodRef <- addMethodRef termType mName mParamTyps (show mTyp)
  let byteCode = toLazyByteString (lazyByteString methodInvocationTermByteCode <>
                   lazyByteString methodInvocationTerms <>
                   (if isStatic then word8 0xb8 else word8 0xb6) <>
                   word16BE methodRef)
  return (byteCode, max termMaxStack (argumentListMaxStack+(if isStatic then 0 else 1)))

generateTermListCode :: [(Type,TypedTerm)] -> ConstantPoolST (B.ByteString, Word16)
generateTermListCode = generateTermListCode' mempty 0 0

{--We use to Word16 values to track the maximum stack required to evaluate the term list. As we move through the
   list, we add a value to the startStack because every term on the list leaves a value on the stack. We also track
   the maximum stack required to evaluate each term plus the increasing with each term startStack. -}
generateTermListCode' :: Builder -> Word16 -> Word16 -> [(Type, TypedTerm)] -> ConstantPoolST (B.ByteString, Word16)
generateTermListCode' b startStack maxStack [] = return (toLazyByteString b, maxStack)
generateTermListCode' b startStack maxStack ((p,t):ps) = do
  (termByteCode, maxStack') <- generateTermCode' t
  unboxingByteCode <- case getTypedTermType t of
    I -> return B.empty
    Z -> return B.empty
    L qn ->
      case p of
        I -> generateTermUnboxingByteCode qn
        Z -> generateTermUnboxingByteCode qn
        L qn -> return B.empty
        Unsupported txt -> undefined
    Unsupported txt -> undefined
  generateTermListCode' (b <> lazyByteString termByteCode <> lazyByteString unboxingByteCode) (startStack+1) (max maxStack (maxStack' + startStack)) ps

generateSuperInvocation :: P.QualifiedName -> [(Type,TypedTerm)] -> ConstantPoolST (B.ByteString, Word16)
generateSuperInvocation parentCls terms = do
  (invocationTerms, maxStack) <- generateTermListCode terms
  let tps = fmap fst terms
  methodRef <- addMethodRef parentCls P.createNameInit tps "V"
  let byteCode = toLazyByteString (
                   word8 0x2a <>
                   lazyByteString invocationTerms <>
                   word8 0xb7 <> word16BE methodRef)
  return (byteCode, maxStack+1)

generateTermBoxingByteCode :: TypedTerm -> ConstantPoolST B.ByteString
generateTermBoxingByteCode typedTerm = do
  case getTypedTermType typedTerm of
    I -> do
      methodRef <- addMethodRef' P.createQNameInteger (P.constructSimpleName (T.pack "valueOf")) "(I)Ljava/lang/Integer;" "java/lang/Integer:valueOf(I)"
      return (toLazyByteString (word8 0xb8 <> word16BE methodRef)) -- invokestatic MethodRef
    Z -> do
      methodRef <- addMethodRef' P.createQNameBoolean (P.constructSimpleName (T.pack "valueOf")) "(Z)Ljava/lang/Boolean;" "java/lang/Boolean:valueOf(Z)"
      return (toLazyByteString (word8 0xb8 <> word16BE methodRef)) -- invokestatic MethodRef
    L qn -> return B.empty
    Unsupported t -> trace ("Unexpected boxing term type: "++show t) undefined

generateTermUnboxingByteCode :: P.QualifiedName -> ConstantPoolST B.ByteString
generateTermUnboxingByteCode refType = do
  methodRef <- case refType of
    qn | qn == P.createQNameInteger ->
      addMethodRef' P.createQNameInteger (P.constructSimpleName (T.pack "intValue")) "()I" "java/lang/Integer:intValue()"
    qn | qn == P.createQNameBoolean ->
      addMethodRef' P.createQNameBoolean (P.constructSimpleName (T.pack "booleanValue")) "()Z" "java/lang/Boolean:booleanValue()"
    qn -> trace ("Unexpected unboxing term type: "++show qn) undefined
  return (toLazyByteString (word8 0xb6 <> word16BE methodRef)) -- invokevirtual MethodRef

generateLoadReference :: Word8 -> B.ByteString
generateLoadReference 0 = toLazyByteString (word8 0x2a)
generateLoadReference 1 = toLazyByteString (word8 0x2b)
generateLoadReference 2 = toLazyByteString (word8 0x2c)
generateLoadReference 3 = toLazyByteString (word8 0x2d)
generateLoadReference p = toLazyByteString (word8 0x19 <> word8 p)
