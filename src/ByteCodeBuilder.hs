{-# LANGUAGE RecordWildCards #-}

module ByteCodeBuilder
  ( buildClass
  ) where

import qualified Data.ByteString.Lazy as B
import Data.ByteString.Builder
import Control.Monad.Trans.State
import Control.Monad (foldM)
import Data.Int
import Data.Word
import Data.List ( foldl' )
import qualified Data.Text as T

import ConstantPoolBuilder
import Parser2
import qualified Parser as P
import qualified Parser2 as P2
import TypeChecker
import Debug.Trace
import Control.Monad.Trans.Class (lift)
import StackMapBuilder
import TypeCheckerTypes
import TypeValidator
import TypeInfo (Type(..),eraseParameterizedType,getErasedType, getClassTypeInfo', getErasedMethodSignature, isTypeParameterized)
import qualified ClassPath as CP

areturn = 0xb0 :: Word8
putfield = 0xb5 :: Word8

data MethodState = MethodState { initialStackMapFrame :: StackMapFrame
                               , stackTypes :: [Type]
                               , pendingStackMapFrame :: Maybe StackMapFrame
                               } deriving Show

type MethodST = StateT MethodState ConstantPoolST

newMethodState :: P.QualifiedName -> [ValidTypeParameter] -> MethodState
newMethodState className params = MethodState { initialStackMapFrame = startingStackFrame className params
                                              , stackTypes = []
                                              , pendingStackMapFrame = Nothing
                                              }

data ClassByteCode = ClassByteCode { accessFlags :: Word16
                                   , classNdx :: Word16
                                   , superNdx :: Word16
                                   , fields :: [B.ByteString]
                                   , methods :: [B.ByteString]
                                   }

buildClass :: TypedClazz -> B.ByteString
buildClass clazz =
  let (ClassByteCode {..}, cp) = runState (buildClass' clazz) newConstantPool in
  B.concat [ classHeader
           , toLazyByteString (word16BE (getCount cp))
           , toBytes cp
           , toLazyByteString (word16BE accessFlags)
           , toLazyByteString (word16BE classNdx)
           , toLazyByteString (word16BE superNdx)
           , toLazyByteString (word16BE 0x0000)
           , toLazyByteString (word16BE (fromIntegral (length fields) :: Word16))
           , B.concat fields
           , toLazyByteString (word16BE (fromIntegral (length methods) :: Word16))
           , B.concat methods
           , toLazyByteString (word16BE 0x0000)]

buildClass' :: TypedClazz -> ConstantPoolST ClassByteCode
buildClass' clazz@(NewTypedClazz accessFlags nameVtn parentVtn fields methods) = do
  clazzNdx <- addClass (getValidTypeQName nameVtn)
  parentNdx <- addClass (getValidTypeQName parentVtn)
  fieldsInfo <- mapM buildFieldInfo fields
  methodsInfo <- mapM (buildMethodInfo (getValidTypeQName nameVtn)) methods
  return $ ClassByteCode {accessFlags=accessFlagWord accessFlags, classNdx=clazzNdx, superNdx=parentNdx, fields=fieldsInfo, methods=methodsInfo}

classHeader :: B.ByteString
classHeader = toLazyByteString (word32BE 0xCAFEBABE <> word16BE 0x0000 <> word16BE 0x0037)

buildFieldInfo :: ValidTypeField -> ConstantPoolST B.ByteString
buildFieldInfo ValidTypeField {..} = do
  let (name,_) = vfName
  nameNdx <- addUtf8 (show name)
  descriptorNdx <- addUtf8 (show (eraseParameterizedType vfType))
  let signature = 
        if isTypeParameterized (L vfType)
          then
            Just (show vfType)
          else
            Nothing
  attributes <- 
        case signature of
          Nothing -> return $ word16BE 0x0000
          Just signature -> do
            attributeNameNdx <- addUtf8 "Signature"
            signatureNdx <- addUtf8 signature
            return $ word16BE 0x0001 <> word16BE attributeNameNdx <> word32BE 0x00000002 <> word16BE signatureNdx
  return $ toLazyByteString (word16BE 0x0001 <> word16BE nameNdx <> word16BE descriptorNdx <> attributes)

buildMethodInfo :: P.QualifiedName -> TypedMethod -> ConstantPoolST B.ByteString
buildMethodInfo className method@(NewTypedMethod name params tp maybeMethodImpl) = do
  let rtrnType = if name == P.createNameInit then "V" else show (eraseParameterizedType tp)
  let descriptor = "("++foldr (\ValidTypeParameter {..} d -> show (eraseParameterizedType vpType)++d) "" params++")"++rtrnType
  nameNdx <- addUtf8 (show name)
  descriptorNdx <- addUtf8 descriptor
  let accessFlagsBuilder = case maybeMethodImpl of
        Nothing -> word16BE 0x0401
        Just _ -> word16BE 0x0001
  (codeAttrInfo,methodState) <- runStateT (buildMethodCodeAttrInfo method) (newMethodState className params)
  let isReturnTypeParameterized = isTypeParameterized (L tp)
      areParamTypesParameterized = foldl' 
        (\accum ValidTypeParameter {..} -> if accum then accum else isTypeParameterized (L vpType)) 
        False 
        params
      signature = 
        if isReturnTypeParameterized || areParamTypesParameterized
          then
            Just ("("++foldl' (\str ValidTypeParameter {..} -> str++show (L vpType)) "" params++")"++show (L tp))
          else
            Nothing
  sigAttribute <- 
        case signature of
          Nothing -> return $ mempty
          Just signature -> do
            attributeNameNdx <- addUtf8 "Signature"
            signatureNdx <- addUtf8 signature
            return $ word16BE attributeNameNdx <> word32BE 0x00000002 <> word16BE signatureNdx
  let attributeCount = (case maybeMethodImpl of Just _ -> 1; Nothing -> 0) +
                       (case signature of Just _ -> 1; Nothing -> 0)
  return $ toLazyByteString (
    accessFlagsBuilder <>
    word16BE nameNdx <>
    word16BE descriptorNdx <>
    word16BE attributeCount <>
    codeAttrInfo <>
    sigAttribute)

buildMethodCodeAttrInfo :: TypedMethod -> MethodST Builder
buildMethodCodeAttrInfo (NewTypedMethod _ params returnType (Just (TypedMethodImpl term))) = do
  (byteCodeChunks, maxStack) <- generateTermCode term
  boxCodeByteChunks <- generateTermConversionByteCode term (L returnType)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let returnCodeByteChunk = ConstantByteCodeChunk (B.singleton areturn) pendingStackMapFrame
  let completeByteCodeChunks = returnCodeByteChunk:boxCodeByteChunks++byteCodeChunks
  stackMapBytes <- lift $ generateStackMapTable completeByteCodeChunks
  let codeBytes = transformRelativeOffsets completeByteCodeChunks
  lift $ buildCodeAttrInfo maxStack
    (fromIntegral (length params) :: Word16)
    (B.concat (reverse codeBytes))
    stackMapBytes
buildMethodCodeAttrInfo (NewTypedMethod _ params _ (Just (TypedConstructorImpl (NewTypedConstructorInvocation cls targetTermTypes terms) assignments))) = do
  (constructorInvocationCodeByteChunks, superInvocationMaxStack) <- generateConstructorInvocation (getValidTypeQName cls) (zip targetTermTypes terms)
  (assignmentCodeByteChunksList, assignmentMaxStack) <- foldM (\(list,ms) a -> fmap (\(c, ms') -> (c:list, max ms ms')) (generateAssignmentCode a)) ([],0) assignments
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let codeByteChunks = concat $ assignmentCodeByteChunksList++[constructorInvocationCodeByteChunks]
  let completeByteCodeChunks = ConstantByteCodeChunk (toLazyByteString (word8 0xb1)) pendingStackMapFrame:codeByteChunks
  stackMapBytes <- lift $ generateStackMapTable completeByteCodeChunks
  let codeBytes = transformRelativeOffsets completeByteCodeChunks
  lift $ buildCodeAttrInfo (max superInvocationMaxStack assignmentMaxStack)
    (fromIntegral (length params) :: Word16)
    (B.concat (reverse codeBytes))
    stackMapBytes
buildMethodCodeAttrInfo (NewTypedMethod _ _ _ Nothing) = return mempty

buildCodeAttrInfo :: Word16 -> Word16 -> B.ByteString -> [B.ByteString] -> ConstantPoolST Builder
buildCodeAttrInfo maxStack paramsCount codeBytes stackMapBytesList = do
  nameNdx <- addUtf8 "Code"
  stackMapTableAttribute <- createStackTableAttribute stackMapBytesList
  let codeBytesLength = (fromIntegral (B.length codeBytes) :: Word32)
  let stackMapAttributeLength = (fromIntegral (B.length stackMapTableAttribute) :: Word32)
  let codeAttributeInfoLength =  codeBytesLength + stackMapAttributeLength + 12
  return $ 
    word16BE nameNdx <>
    word32BE codeAttributeInfoLength <>
    word16BE maxStack <>
    word16BE (paramsCount+1) <>
    word32BE codeBytesLength <>
    lazyByteString codeBytes <>
    word16BE 0x0000 <> {-- Exception table length -}
    if null stackMapBytesList then word16BE 0x0000 else word16BE 0x0001 <> lazyByteString stackMapTableAttribute   {-- Attributes table length -}

generateAssignmentCode :: TypedAssignment -> MethodST ([ByteCodeChunk], Word16)
generateAssignmentCode (NewTypedAssignment lhTerm rhTerm) = generateAssignmentCode' lhTerm rhTerm

generateAssignmentCode' :: TypedTerm -> TypedTerm -> MethodST ([ByteCodeChunk], Word16)
generateAssignmentCode' (TypedApplication (TypedReferenceTerm (TypeCheckerClassReferenceTypeWrapper typedReferenceTermVtn _) t) TypedFieldAccess {fName=field, fTyp=tp}) rhTerm= do
  (lhByteCode, lhMaxStack) <- generateTermCode t
  (rhByteCode, rhMaxStack) <- generateTermCode rhTerm
  fieldRef <- lift $ addFieldRef (getValidTypeQName typedReferenceTermVtn) field (getErasedType [] tp)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = [ConstantByteCodeChunk (toLazyByteString (word8 putfield <> word16BE fieldRef)) pendingStackMapFrame]++
                 rhByteCode++
                 lhByteCode
  return (byteCode, max lhMaxStack (rhMaxStack+1))
generateAssignmentCode' _ _ = undefined

generateTermCode :: TypedTerm -> MethodST ([ByteCodeChunk], Word16)
generateTermCode = generateTermCode'

generateTermCode' :: TypedTerm -> MethodST ([ByteCodeChunk], Word16)
generateTermCode' (TypedValue TypedVariable {vPosition=p, vTyp=tp}) = do
  let byteCode = generateLoadReference p
  pendingStackMapFrame <- getPossiblePendingStackFrame
  modify (\MethodState {..} -> MethodState {stackTypes=tp:stackTypes,..})
  return ([ConstantByteCodeChunk byteCode pendingStackMapFrame], 1)
generateTermCode' (TypedValue TypedIntegerLiteral {iValue=value}) = do
  intNdx <- lift $ addInteger value
  methodRef <- lift $ addSimpleMethodRef P.createQNameInteger (P.constructSimpleName (T.pack "valueOf")) "(I)Ljava/lang/Integer;" "java/lang/Integer:valueOf(I)"
  let byteCode = toLazyByteString (
                   word8 0x13 <> word16BE intNdx <>  -- ldc_w Integer Constant
                   word8 0xb8 <> word16BE methodRef) -- invokestatic MethodRef
  pendingStackMapFrame <- getPossiblePendingStackFrame
  modify (\MethodState {..} -> MethodState {stackTypes=L CP.createValidTypeClassTypeInteger : stackTypes,..})
  return ([ConstantByteCodeChunk byteCode pendingStackMapFrame], 1)
generateTermCode' (TypedValue TypedStringLiteral {sValue=value}) = do
  strNdx <- lift $ addString value
  let byteCode = toLazyByteString (
                   word8 0x13 <> word16BE strNdx) -- ldc_w String Constant
  pendingStackMapFrame <- getPossiblePendingStackFrame
  modify (\MethodState {..} -> MethodState {stackTypes=L CP.createValidTypeClassTypeString : stackTypes,..})
  return ([ConstantByteCodeChunk byteCode pendingStackMapFrame], 1)
generateTermCode' (TypedValue TypedBooleanLiteral {bValue=value}) = do
  methodRef <- lift $ addSimpleMethodRef P.createQNameBoolean (P.constructSimpleName (T.pack "valueOf")) "(Z)Ljava/lang/Boolean;" "java/lang/Boolean:valueOf(Z)"
  let byteCode = toLazyByteString (
                   (if value then word8 0x04 else word8 0x03) <> -- iconst_1 (true) or iconst_0 (false) 
                   word8 0xb8 <> word16BE methodRef)                           -- invokestatic MethodRef
  pendingStackMapFrame <- getPossiblePendingStackFrame
  modify (\MethodState {..} -> MethodState {stackTypes=L CP.createValidTypeClassTypeBoolean : stackTypes,..})
  return ([ConstantByteCodeChunk byteCode pendingStackMapFrame], 1)
generateTermCode' (TypedValue TypedObjectCreation {ocTyp=vtn@(TypeCheckerClassReferenceTypeWrapper tpVtn _), ocParamTyps=targetParamTypes, ocTerms=terms}) = do
  pendingStackMapFrame <- getPossiblePendingStackFrame
  classNdx <- lift $ addClass (getValidTypeQName tpVtn)
  (constructorTerms, maxStack) <- generateTermListCode (zip targetParamTypes terms)
  pendingParametersStackMapFrame <- getPossiblePendingStackFrame
  modify (\MethodState {..} -> MethodState {stackTypes=drop (length targetParamTypes) stackTypes,..})
  constructorMethodRef <- lift $ addMethodRef (getValidTypeQName tpVtn) P.createNameInit (fmap getTypedTermType terms) "V"
  let byteCode = [ConstantByteCodeChunk (toLazyByteString (word8 0xb7 <> word16BE constructorMethodRef)) pendingParametersStackMapFrame]++
                 constructorTerms++
                 [ConstantByteCodeChunk (toLazyByteString (word8 0xbb <> word16BE classNdx <> word8 0x59)) pendingStackMapFrame]
  modify (\MethodState {..} -> MethodState {stackTypes=L vtn : stackTypes,..})
  return (byteCode, maxStack+2) {--Add 2 for the new object ref and the duplicate -}
generateTermCode' (TypedCast (TypedReferenceTerm (TypeCheckerClassReferenceTypeWrapper tpVtn _) term)) = do
  classNdx <- lift $ addClass (getValidTypeQName tpVtn)
  (castTermByteCode, maxStack) <- generateTermCode' term
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = ConstantByteCodeChunk (toLazyByteString (word8 0xc0 <> word16BE classNdx)) pendingStackMapFrame:castTermByteCode
  return (byteCode, maxStack)
generateTermCode' (TypedApplication (TypedReferenceTerm (TypeCheckerClassReferenceTypeWrapper termTypeVtn _) term) TypedFieldAccess {fName=name, fTyp=tp}) = do
  (applicationTermByteCode, maxStack) <- generateTermCode' term
  fieldRef <- lift $ addFieldRef (getValidTypeQName termTypeVtn) name (getErasedType [] tp) -- TODO: fix when TypeVariables supported.
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = ConstantByteCodeChunk (toLazyByteString (word8 0xb4 <> word16BE fieldRef)) pendingStackMapFrame:applicationTermByteCode
  modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..})
  return (byteCode, maxStack)
generateTermCode' (TypedApplication (TypedReferenceTerm (TypeCheckerClassReferenceTypeWrapper termTypeVtn typeArgs) term) TypedMethodInvocation {..}) = do
  (methodInvocationTermByteCode, termMaxStack) <- generateTermCode' term
  (methodInvocationTerms, argumentListMaxStack) <- generateTermListCode (zip mArgumentTyps mArgumentTerms)
  methodRef <- lift $ addMethodRef (getValidTypeQName termTypeVtn) mName mErasedArgumentTypes (show mErasedType)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = [ConstantByteCodeChunk (toLazyByteString (word8 0xb6 <> word16BE methodRef)) pendingStackMapFrame]++
                 methodInvocationTerms++
                 methodInvocationTermByteCode
  modify (\MethodState {..} -> MethodState {stackTypes=mErasedType:drop (length mArgumentTyps+1) stackTypes,..})
  return (byteCode, max termMaxStack (argumentListMaxStack+1))
generateTermCode' (TypedApplication (TypedReferenceTerm (TypeCheckerClassReferenceTypeWrapper termTypeVtn typeArgs) term) TypedInterfaceMethodInvocation {..}) = do
  (methodInvocationTermByteCode, termMaxStack) <- generateTermCode' term
  (methodInvocationTerms, argumentListMaxStack) <- generateTermListCode (zip iArgumentTyps iArgumentTerms)
  interfaceMethodRef <- lift $ addInterfaceMethodRef (getValidTypeQName termTypeVtn) iName iErasedArgumentTypes (show iErasedType)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = [ConstantByteCodeChunk
                   (toLazyByteString (word8 0xb9 <> 
                      word16BE interfaceMethodRef <> 
                      word8 (fromIntegral (length iArgumentTyps+1) :: Word8) <> 
                      word8 0))
                   pendingStackMapFrame]++
                 methodInvocationTerms++
                 methodInvocationTermByteCode
  modify (\MethodState {..} -> MethodState {stackTypes=iErasedType:drop (length iArgumentTyps+1) stackTypes,..})
  return (byteCode, max termMaxStack (argumentListMaxStack+1))
generateTermCode' (TypedApplication (TypedReferenceTerm (TypeCheckerClassReferenceTypeWrapper termTypeVtn _) term) TypedSuperMethodInvocation {..}) = do
  (methodInvocationTermByteCode, termMaxStack) <- generateTermCode' term
  (methodInvocationTerms, argumentListMaxStack) <- generateTermListCode (zip smParamTyps smTerms)
  methodRef <- lift $ addMethodRef (getValidTypeQName termTypeVtn) smName smParamTyps (show (getErasedType [] smTyp))
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = [ConstantByteCodeChunk (toLazyByteString (word8 0xb7 <> word16BE methodRef)) pendingStackMapFrame]++ {-- invokespecial -}
                 methodInvocationTerms++
                 methodInvocationTermByteCode
  modify (\MethodState {..} -> MethodState {stackTypes=smTyp:drop (length smParamTyps+1) stackTypes,..})
  return (byteCode, max termMaxStack (argumentListMaxStack+1))
generateTermCode' (TypedStaticApplication (TypedTypeName tnQnVtn) TypedStaticFieldAccess {tfName=name, tfTyp=tp}) = do
  fieldRef <- lift $ addFieldRef (getValidTypeQName tnQnVtn) name tp
  let byteCode = ConstantByteCodeChunk (toLazyByteString (word8 0xb2 <> word16BE fieldRef)) Nothing
  modify (\MethodState {..} -> MethodState {stackTypes=tp:stackTypes,..})
  return ([byteCode], 1)
generateTermCode' (TypedStaticApplication (TypedTypeName tnQnVtn) TypedStaticMethodInvocation {..}) = do
  (methodInvocationTerms, argumentListMaxStack) <- generateTermListCode (zip tmParamTyps tmTerms)
  methodRef <- lift $ addMethodRef (getValidTypeQName tnQnVtn) tmName tmParamTyps (show tmTyp)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = ConstantByteCodeChunk (toLazyByteString (word8 0xb8 <> word16BE methodRef)) pendingStackMapFrame:methodInvocationTerms
  modify (\MethodState {..} -> MethodState {stackTypes=tmTyp:drop (length tmParamTyps) stackTypes,..})
  return (byteCode, max 1 argumentListMaxStack)
generateTermCode' (TypedConditional booleanTerm thenTerm elseTerm tp) = do
  MethodState {stackTypes=originalStackTypes,..} <- get
  (booleanTermCode, booleanMaxStack) <- generateTermCode booleanTerm
  booleanTermConversionCode <- generateTermConversionByteCode booleanTerm Z
  modify (\MethodState {..} -> MethodState {stackTypes=originalStackTypes,pendingStackMapFrame=Nothing,..})
  (thenTermCode, thenMaxStack) <- generateTermCode thenTerm
  thenTermConversionCode <- generateTermConversionByteCode thenTerm tp
  let elseTermStackMapFrame = addStackMapFrame initialStackMapFrame originalStackTypes
  modify (\MethodState {..} -> MethodState {stackTypes=originalStackTypes,pendingStackMapFrame=Just elseTermStackMapFrame,..})
  (elseTermCode, elseMaxStack) <- generateTermCode elseTerm
  elseTermConversionCode <- generateTermConversionByteCode elseTerm tp
  MethodState {..} <- get
  let remainderTermStackMapFrame = addStackMapFrame initialStackMapFrame stackTypes
  modify (\MethodState {..} -> MethodState {pendingStackMapFrame=Just remainderTermStackMapFrame,..})
  let byteCode = elseTermConversionCode++elseTermCode++
          [ConstantByteCodeChunk (toLazyByteString (word8 0xC8 <>
            word32BE (fromIntegral (chunkListBytes (elseTermConversionCode++elseTermCode)+5)))) Nothing]++ -- goto_w
          thenTermConversionCode++thenTermCode++
          [ConstantByteCodeChunk (toLazyByteString (word8 0x99 <>
            word16BE (fromIntegral (chunkListBytes (thenTermConversionCode++thenTermCode)+3+5)))) Nothing]++ -- if<cond>
          booleanTermConversionCode++booleanTermCode
  return (byteCode, max booleanMaxStack (max thenMaxStack elseMaxStack))

generateTermListCode :: [(Type,TypedTerm)] -> MethodST ([ByteCodeChunk], Word16)
generateTermListCode = generateTermListCode' [] 0 0

{--We use to Word16 values to track the maximum stack required to evaluate the term list. As we move through the
   list, we add a value to the startStack because every term on the list leaves a value on the stack. We also track
   the maximum stack required to evaluate each term plus the increasing with each term startStack. -}
generateTermListCode' :: [ByteCodeChunk] -> Word16 -> Word16 -> [(Type, TypedTerm)] -> MethodST ([ByteCodeChunk], Word16)
generateTermListCode' b startStack maxStack [] = return (b, maxStack)
generateTermListCode' b startStack maxStack ((p,t):ps) = do
  (termByteCode, maxStack') <- generateTermCode' t
  conversionByteCode <- generateTermConversionByteCode t p
  generateTermListCode' (conversionByteCode++termByteCode++b) (startStack+1) (max maxStack (maxStack' + startStack)) ps

generateConstructorInvocation :: QualifiedName -> [(Type,TypedTerm)] -> MethodST ([ByteCodeChunk], Word16)
generateConstructorInvocation clsQn terms = do
  (invocationTerms, maxStack) <- generateTermListCode terms
  let tps = fmap fst terms
  methodRef <- lift $ addMethodRef clsQn P.createNameInit tps "V"
  let byteCode = [ConstantByteCodeChunk (toLazyByteString (word8 0xb7 <> word16BE methodRef)) Nothing]++
                 invocationTerms++
                 [ConstantByteCodeChunk (toLazyByteString (word8 0x2a)) Nothing]
  return (byteCode, maxStack+1)

{-- Generates bytecoe to box or unbox a term based on the required type -}
generateTermConversionByteCode :: TypedTerm -> Type -> MethodST [ByteCodeChunk]
generateTermConversionByteCode typedTerm tp =
  case getTypedTermType typedTerm of
    I -> case tp of
      (L (TypeCheckerClassReferenceTypeWrapper vtn _)) -> do modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..}); generateTermBoxingByteCode (getValidTypeQName vtn)
      _      -> return [ConstantByteCodeChunk B.empty Nothing]
    Z -> case tp of
      (L (TypeCheckerClassReferenceTypeWrapper vtn _)) -> do modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..}); generateTermBoxingByteCode (getValidTypeQName vtn)
      _      -> return [ConstantByteCodeChunk B.empty Nothing]
    L (TypeCheckerClassReferenceTypeWrapper vtn _) -> case tp of
      I -> do modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..}); generateTermUnboxingByteCode (getValidTypeQName vtn)
      Z -> do modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..}); generateTermUnboxingByteCode (getValidTypeQName vtn)
      _ -> do modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..}); return [ConstantByteCodeChunk B.empty Nothing]
    _    -> trace "Unexpected boxing term type" undefined

generateTermBoxingByteCode :: P.QualifiedName -> MethodST [ByteCodeChunk]
generateTermBoxingByteCode refType = do
  methodRef <- case refType of
    qn | qn == P.createQNameInteger ->
      lift $ addSimpleMethodRef P.createQNameInteger (P.constructSimpleName (T.pack "valueOf")) "(I)Ljava/lang/Integer;" "java/lang/Integer:valueOf(I)"
    qn | qn == P.createQNameBoolean ->
      lift $ addSimpleMethodRef P.createQNameBoolean (P.constructSimpleName (T.pack "valueOf")) "(Z)Ljava/lang/Boolean;" "java/lang/Boolean:valueOf(Z)"
    qn -> trace ("Unexpected boxing term type: "++show qn) undefined
  let byteCode = toLazyByteString (word8 0xb8 <> word16BE methodRef)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  return [ConstantByteCodeChunk byteCode pendingStackMapFrame] -- invokestatic MethodRef

generateTermUnboxingByteCode :: P.QualifiedName -> MethodST [ByteCodeChunk]
generateTermUnboxingByteCode refType = do
  methodRef <- case refType of
    qn | qn == P.createQNameInteger ->
      lift $ addSimpleMethodRef P.createQNameInteger (P.constructSimpleName (T.pack "intValue")) "()I" "java/lang/Integer:intValue()"
    qn | qn == P.createQNameBoolean ->
      lift $ addSimpleMethodRef P.createQNameBoolean (P.constructSimpleName (T.pack "booleanValue")) "()Z" "java/lang/Boolean:booleanValue()"
    qn -> trace ("Unexpected unboxing term type: "++show qn) undefined
  let byteCode = toLazyByteString (word8 0xb6 <> word16BE methodRef)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  return [ConstantByteCodeChunk byteCode pendingStackMapFrame] -- invokevirtual MethodRef

generateLoadReference :: Word8 -> B.ByteString
generateLoadReference 0 = toLazyByteString (word8 0x2a)
generateLoadReference 1 = toLazyByteString (word8 0x2b)
generateLoadReference 2 = toLazyByteString (word8 0x2c)
generateLoadReference 3 = toLazyByteString (word8 0x2d)
generateLoadReference p = toLazyByteString (word8 0x19 <> word8 p)

data ByteCodeChunk = ConstantByteCodeChunk B.ByteString (Maybe StackMapFrame) deriving Show

transformRelativeOffsets :: [ByteCodeChunk] -> [B.ByteString]
transformRelativeOffsets byteStrings =
  snd $ foldr transformRelativeOffsets' (0, []) byteStrings

transformRelativeOffsets' :: ByteCodeChunk -> (Int64,[B.ByteString]) -> (Int64, [B.ByteString])
transformRelativeOffsets' chunk (bytePos,acc) =
  case chunk of
    ConstantByteCodeChunk bs _ -> (bytePos+B.length bs,bs:acc)

generateStackMapTable :: [ByteCodeChunk] -> ConstantPoolST [B.ByteString]
generateStackMapTable byteCodeChunks = do
  let fullStackMapFrames = fmap snd $ snd $ foldr generateStackMapTable' (0, []) byteCodeChunks
  mapM createStackMapFrameByteString fullStackMapFrames

generateStackMapTable' :: ByteCodeChunk -> (Int64,[(Int64,StackMapFrameWithOffset)]) -> (Int64, [(Int64,StackMapFrameWithOffset)])
generateStackMapTable' chunk (bytePos,stackFrameTable) =
  case chunk of
    ConstantByteCodeChunk bs (Just frame) ->
      case stackFrameTable of
        [] -> (bytePos+B.length bs, [(bytePos, StackMapFrameWithOffset bytePos frame)])
        (lastFrameBytePos,_) : _ -> (bytePos+B.length bs, (bytePos, StackMapFrameWithOffset (bytePos-(lastFrameBytePos+1)) frame) : stackFrameTable)
    ConstantByteCodeChunk bs Nothing -> (bytePos+B.length bs,stackFrameTable)

chunkListBytes :: [ByteCodeChunk] -> Int64
chunkListBytes = foldr chunkBytes 0

chunkBytes :: ByteCodeChunk -> Int64 -> Int64
chunkBytes (ConstantByteCodeChunk bs _) acc = acc+B.length bs

getPossiblePendingStackFrame :: MethodST (Maybe StackMapFrame)
getPossiblePendingStackFrame = do
  MethodState {..} <- get
  modify (\MethodState {..} -> MethodState {pendingStackMapFrame=Nothing,..})
  return pendingStackMapFrame

accessFlagWord :: [P.ClassAccessFlag] -> Word16
accessFlagWord = foldl' (\w a -> w + case a of P.CPublic -> 0x0001; P.CInterface -> 0x0200; P.CAbstract -> 0x0400) 0