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
import TypeInfo
import qualified Parser as P
import qualified Parser2 as P2
import TypeChecker
import Debug.Trace
import Control.Monad.Trans.Class (lift)
import StackMapBuilder

data MethodState = MethodState { initialStackMapFrame :: StackMapFrame
                               , stackTypes :: [Type]
                               , pendingStackMapFrame :: Maybe StackMapFrame
                               } deriving Show

type MethodST = StateT MethodState ConstantPoolST

newMethodState :: P.QualifiedName -> [P2.Parameter] -> MethodState
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
  methodsInfo <- mapM (buildMethodInfo name) methods
  return $ ClassByteCode {accessFlags=0x0001, classNdx=clazzNdx, superNdx=parentNdx, fields=fieldsInfo, methods=methodsInfo}

classHeader :: B.ByteString
classHeader = toLazyByteString (word32BE 0xCAFEBABE <> word16BE 0x0000 <> word16BE 0x0037)

buildFieldInfo :: Field -> ConstantPoolST B.ByteString
buildFieldInfo (NewField _ tp _ name) = do
  nameNdx <- addUtf8 (show name)
  descriptorNdx <- addUtf8 ("L"++show tp++";")
  return $ toLazyByteString (word16BE 0x0001 <> word16BE nameNdx <> word16BE descriptorNdx <> word16BE 0x0000)

buildMethodInfo :: P.QualifiedName -> TypedMethod -> ConstantPoolST B.ByteString
buildMethodInfo className method@(NewTypedMethod name params tp _) = do
  let rtrnType = if name == P.createNameInit then "V" else "L"++show tp++";"
  let descriptor = "("++foldr (\(NewParameter _ ptype _) d -> ("L"++show ptype++";")++d) "" params++")"++rtrnType
  nameNdx <- addUtf8 (show name)
  descriptorNdx <- addUtf8 descriptor
  (codeAttrInfo,methodState) <- runStateT (buildMethodCodeAttrInfo method) (newMethodState className params)
  return $ toLazyByteString (word16BE 0x0001 <> word16BE nameNdx <> word16BE descriptorNdx <> word16BE 0x0001 <> lazyByteString codeAttrInfo)

buildMethodCodeAttrInfo :: TypedMethod -> MethodST B.ByteString
buildMethodCodeAttrInfo (NewTypedMethod _ params returnType (TypedMethodImpl term)) = do
  (byteCodeChunks, maxStack) <- generateTermCode term
  boxCodeByteChunks <- generateTermConversionByteCode term (L returnType CompiledCode)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let returnCodeByteChunk = ConstantByteCodeChunk (toLazyByteString (word8 0xb0)) pendingStackMapFrame
  let completeByteCodeChunks = returnCodeByteChunk:boxCodeByteChunks++byteCodeChunks
  stackMapBytes <- lift $ generateStackMapTable completeByteCodeChunks
  let codeBytes = transformRelativeOffsets completeByteCodeChunks
  lift $ buildCodeAttrInfo maxStack
    (fromIntegral (length params) :: Word16)
    (B.concat (reverse codeBytes))
    stackMapBytes
buildMethodCodeAttrInfo (NewTypedMethod _ params _ (TypedConstructorImpl (NewTypedConstructorInvocation cls targetTermTypes terms) assignments)) = do
  (constructorInvocationCodeByteChunks, superInvocationMaxStack) <- generateConstructorInvocation cls (zip targetTermTypes terms)
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

buildCodeAttrInfo :: Word16 -> Word16 -> B.ByteString -> [B.ByteString] -> ConstantPoolST B.ByteString
buildCodeAttrInfo maxStack paramsCount codeBytes stackMapBytesList = do
  nameNdx <- addUtf8 "Code"
  stackMapTableAttribute <- createStackTableAttribute stackMapBytesList
  let codeBytesLength = (fromIntegral (B.length codeBytes) :: Word32)
  let stackMapAttributeLength = (fromIntegral (B.length stackMapTableAttribute) :: Word32)
  let codeAttributeInfoLength =  codeBytesLength + stackMapAttributeLength + 12
  return $ toLazyByteString (
    word16BE nameNdx <>
    word32BE codeAttributeInfoLength <>
    word16BE maxStack <>
    word16BE (paramsCount+1) <>
    word32BE codeBytesLength <>
    lazyByteString codeBytes <>
    word16BE 0x0000 <> {-- Exception table length -}
    if null stackMapBytesList then word16BE 0x0000 else word16BE 0x0001 <> lazyByteString stackMapTableAttribute)   {-- Attributes table length -}

generateAssignmentCode :: TypedAssignment -> MethodST ([ByteCodeChunk], Word16)
generateAssignmentCode (NewTypedAssignment lhTerm rhTerm) = generateAssignmentCode' lhTerm rhTerm

generateAssignmentCode' :: TypedTerm -> TypedTerm -> MethodST ([ByteCodeChunk], Word16)
generateAssignmentCode' (TypedApplication (TypedReferenceTerm termTypeName t) TypedFieldAccess {fName=field, fTyp=tp}) rhTerm= do
  (lhByteCode, lhMaxStack) <- generateTermCode t
  (rhByteCode, rhMaxStack) <- generateTermCode rhTerm
  fieldRef <- lift $ addFieldRef termTypeName field tp
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = [ConstantByteCodeChunk (toLazyByteString (word8 0xb5 <> word16BE fieldRef)) pendingStackMapFrame]++
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
  methodRef <- lift $ addMethodRef' P.createQNameInteger (P.constructSimpleName (T.pack "valueOf")) "(I)Ljava/lang/Integer;" "java/lang/Integer:valueOf(I)"
  let byteCode = toLazyByteString (
                   word8 0x13 <> word16BE intNdx <>  -- ldc_w Integer Constant
                   word8 0xb8 <> word16BE methodRef) -- invokestatic MethodRef
  pendingStackMapFrame <- getPossiblePendingStackFrame
  modify (\MethodState {..} -> MethodState {stackTypes=L P.createQNameInteger P2.CompiledCode : stackTypes,..})
  return ([ConstantByteCodeChunk byteCode pendingStackMapFrame], 1)
generateTermCode' (TypedValue TypedStringLiteral {sValue=value}) = do
  strNdx <- lift $ addString value
  let byteCode = toLazyByteString (
                   word8 0x13 <> word16BE strNdx) -- ldc_w String Constant
  pendingStackMapFrame <- getPossiblePendingStackFrame
  modify (\MethodState {..} -> MethodState {stackTypes=L P.createQNameString P2.CompiledCode:stackTypes,..})
  return ([ConstantByteCodeChunk byteCode pendingStackMapFrame], 1)
generateTermCode' (TypedValue TypedBooleanLiteral {bValue=value}) = do
  methodRef <- lift $ addMethodRef' P.createQNameBoolean (P.constructSimpleName (T.pack "valueOf")) "(Z)Ljava/lang/Boolean;" "java/lang/Boolean:valueOf(Z)"
  let byteCode = toLazyByteString (
                   (if value then word8 0x04 else word8 0x03) <> -- iconst_1 (true) or iconst_0 (false) 
                   word8 0xb8 <> word16BE methodRef)                           -- invokestatic MethodRef
  pendingStackMapFrame <- getPossiblePendingStackFrame
  modify (\MethodState {..} -> MethodState {stackTypes=L P.createQNameBoolean P2.CompiledCode : stackTypes,..})
  return ([ConstantByteCodeChunk byteCode pendingStackMapFrame], 1)
generateTermCode' (TypedValue TypedObjectCreation {ocTyp=tp, ocParamTyps=targetParamTypes, ocTerms=terms}) = do
  pendingStackMapFrame <- getPossiblePendingStackFrame
  classNdx <- lift $ addClass tp
  (constructorTerms, maxStack) <- generateTermListCode (zip targetParamTypes terms)
  pendingParametersStackMapFrame <- getPossiblePendingStackFrame
  modify (\MethodState {..} -> MethodState {stackTypes=drop (length targetParamTypes) stackTypes,..})
  constructorMethodRef <- lift $ addMethodRef tp P.createNameInit (fmap getTypedTermType terms) "V"
  let byteCode = [ConstantByteCodeChunk (toLazyByteString (word8 0xb7 <> word16BE constructorMethodRef)) pendingParametersStackMapFrame]++
                 constructorTerms++
                 [ConstantByteCodeChunk (toLazyByteString (word8 0xbb <> word16BE classNdx <> word8 0x59)) pendingStackMapFrame]
  modify (\MethodState {..} -> MethodState {stackTypes=L tp P2.CompiledCode:stackTypes,..})
  return (byteCode, maxStack+2) {--Add 2 for the new object ref and the duplicate -}
generateTermCode' (TypedCast (TypedReferenceTerm tp term)) = do
  classNdx <- lift $ addClass tp
  (castTermByteCode, maxStack) <- generateTermCode' term
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = ConstantByteCodeChunk (toLazyByteString (word8 0xc0 <> word16BE classNdx)) pendingStackMapFrame:castTermByteCode
  return (byteCode, maxStack)
generateTermCode' (TypedApplication (TypedReferenceTerm termType term) TypedFieldAccess {fName=name, fTyp=tp}) = do
  (applicationTermByteCode, maxStack) <- generateTermCode' term
  fieldRef <- lift $ addFieldRef termType name tp
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = ConstantByteCodeChunk (toLazyByteString (word8 0xb4 <> word16BE fieldRef)) pendingStackMapFrame:applicationTermByteCode
  modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..})
  return (byteCode, maxStack)
generateTermCode' (TypedApplication (TypedReferenceTerm termType term) TypedMethodInvocation {..}) = do
  (methodInvocationTermByteCode, termMaxStack) <- generateTermCode' term
  (methodInvocationTerms, argumentListMaxStack) <- generateTermListCode (zip mParamTyps mTerms)
  methodRef <- lift $ addMethodRef termType mName mParamTyps (show mTyp)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = [ConstantByteCodeChunk (toLazyByteString (word8 0xb6 <> word16BE methodRef)) pendingStackMapFrame]++
                 methodInvocationTerms++
                 methodInvocationTermByteCode
  modify (\MethodState {..} -> MethodState {stackTypes=mTyp:drop (length mParamTyps+1) stackTypes,..})
  return (byteCode, max termMaxStack (argumentListMaxStack+1))
generateTermCode' (TypedStaticApplication (TypeName _ tnQn) TypedFieldAccess {fName=name, fTyp=tp}) = do
  fieldRef <- lift $ addFieldRef tnQn name tp
  let byteCode = ConstantByteCodeChunk (toLazyByteString (word8 0xb2 <> word16BE fieldRef)) Nothing
  modify (\MethodState {..} -> MethodState {stackTypes=tp:stackTypes,..})
  return ([byteCode], 0)
generateTermCode' (TypedStaticApplication (TypeName _ tnQn) TypedMethodInvocation {..}) = do
  (methodInvocationTerms, argumentListMaxStack) <- generateTermListCode (zip mParamTyps mTerms)
  methodRef <- lift $ addMethodRef tnQn mName mParamTyps (show mTyp)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  let byteCode = ConstantByteCodeChunk (toLazyByteString (word8 0xb8 <> word16BE methodRef)) pendingStackMapFrame:methodInvocationTerms
  modify (\MethodState {..} -> MethodState {stackTypes=mTyp:drop (length mParamTyps) stackTypes,..})
  return (byteCode, argumentListMaxStack)
generateTermCode' (TypedConditional booleanTerm thenTerm elseTerm tp) = do
  MethodState {stackTypes=originalStackTypes,..} <- get
  (booleanTermCode, booleanMaxStack) <- generateTermCode booleanTerm
  booleanTermConversionCode <- generateTermConversionByteCode booleanTerm (Z CompiledCode)
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

generateConstructorInvocation :: P.QualifiedName -> [(Type,TypedTerm)] -> MethodST ([ByteCodeChunk], Word16)
generateConstructorInvocation cls terms = do
  (invocationTerms, maxStack) <- generateTermListCode terms
  let tps = fmap fst terms
  methodRef <- lift $ addMethodRef cls P.createNameInit tps "V"
  let byteCode = [ConstantByteCodeChunk (toLazyByteString (word8 0xb7 <> word16BE methodRef)) Nothing]++
                 invocationTerms++
                 [ConstantByteCodeChunk (toLazyByteString (word8 0x2a)) Nothing]
  return (byteCode, maxStack+1)

{-- Generates bytecoe to box or unbox a term based on the required type -}
generateTermConversionByteCode :: TypedTerm -> Type -> MethodST [ByteCodeChunk]
generateTermConversionByteCode typedTerm tp = do
  case getTypedTermType typedTerm of
    I _ -> case tp of
      (L qn _) -> do modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..}); generateTermBoxingByteCode qn
      _        -> return [ConstantByteCodeChunk B.empty Nothing]
    Z _ -> case tp of
      (L qn _) -> do modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..}); generateTermBoxingByteCode qn
      _        -> return [ConstantByteCodeChunk B.empty Nothing]
    L qn _ -> case tp of
        (I _) -> do modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..}); generateTermUnboxingByteCode qn
        (Z _) -> do modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..}); generateTermUnboxingByteCode qn
        _     -> do modify (\MethodState {..} -> MethodState {stackTypes=tp:drop 1 stackTypes,..}); return [ConstantByteCodeChunk B.empty Nothing]
    UnsupportedType _ -> trace "Unexpected boxing term type" undefined

generateTermBoxingByteCode :: P.QualifiedName -> MethodST [ByteCodeChunk]
generateTermBoxingByteCode refType = do
  methodRef <- case refType of
    qn | qn == P.createQNameInteger ->
      lift $ addMethodRef' P.createQNameInteger (P.constructSimpleName (T.pack "valueOf")) "(I)Ljava/lang/Integer;" "java/lang/Integer:valueOf(I)"
    qn | qn == P.createQNameBoolean ->
      lift $ addMethodRef' P.createQNameBoolean (P.constructSimpleName (T.pack "valueOf")) "(Z)Ljava/lang/Boolean;" "java/lang/Boolean:valueOf(Z)"
    qn -> trace ("Unexpected boxing term type: "++show qn) undefined
  let byteCode = toLazyByteString (word8 0xb8 <> word16BE methodRef)
  pendingStackMapFrame <- getPossiblePendingStackFrame
  return [ConstantByteCodeChunk byteCode pendingStackMapFrame] -- invokestatic MethodRef

generateTermUnboxingByteCode :: P.QualifiedName -> MethodST [ByteCodeChunk]
generateTermUnboxingByteCode refType = do
  methodRef <- case refType of
    qn | qn == P.createQNameInteger ->
      lift $ addMethodRef' P.createQNameInteger (P.constructSimpleName (T.pack "intValue")) "()I" "java/lang/Integer:intValue()"
    qn | qn == P.createQNameBoolean ->
      lift $ addMethodRef' P.createQNameBoolean (P.constructSimpleName (T.pack "booleanValue")) "()Z" "java/lang/Boolean:booleanValue()"
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
