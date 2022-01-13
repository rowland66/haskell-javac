{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module TypeInfo
( TypeInfo
, ClassPathSignature(..)
, MethodInvocation(..)
, Type(..)
, getClassTypeInfoE
, isSubtypeOf'
, isSubtypeOfE
, getFieldType
, getTypeName
, getTypeParent
, getMethodType
, getStaticMethodType
, isValidClass
, getBoxedType
, getUnboxedType
, isTypeBoolean
, isTypeInteger
, mapParameterToType
, getSupertypeSet
) where

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.List as List
import Control.Monad.Loops (unfoldrM)
import Control.Monad.Trans.Except ( ExceptT, runExceptT, throwE )
import Control.Monad.ListM (sortByM)
import Data.Bits
import Data.Word
import ClassPath (ClassPath, ClassDescriptor(..), getClass, Field (..), Method (..), hasClass)
import TextShow (toText, showb, showt)
import Control.Monad.Extra ( foldM, ifM, join, filterM )
import Data.Tuple.Sequence ( SequenceT(sequenceT) )
import Data.List (foldl')
import Debug.Trace ( trace )
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT,get,put,runStateT)
import qualified Parser as P
import qualified Parser2 as P2
import Text.Parsec
import qualified Data.Tuple.Extra as Data.Bifunctor

{-- TypeInfo provides type information. A Local TypeInfo provides type information for types defined in the
    code being compiled. Path TypeInfo provides type information for types found on the classspath in compiled
    class files -}
data TypeInfo = Local P2.Clazz2 | Path ClassDescriptor

type ClassData = (ClassPath,P2.LocalClasses)

data ClassPathSignature = ClassPathSignature T.Text [Type] deriving Show

data MethodInvocation = NewMethodInvocation Type ClassPathSignature deriving Show

data Type = I P2.SourcePos' | Z P2.SourcePos' | L P.QualifiedName P2.SourcePos' | UnsupportedType P2.SourcePos'

instance Show Type where
  show (I _) = "I"
  show (Z _) = "Z"
  show (L n _) = "L"++show n++";"
  show (UnsupportedType t) = "Unsupported: "++show t

instance Eq Type where
  (==) (I _) (I _) = True
  (==) (Z _) (Z _) = True
  (==) (L n1 _) (L n2 _) = n1 == n2
  (==) _ _ = False

object = T.pack "java/lang/Object"
rparens = T.pack ")"
semi = T.pack ";"

readType :: T.Text -> Type
readType t | T.unpack (T.take 1 t) == "I" = I P2.CompiledCode
readType t | T.unpack (T.take 1 t) == "Z" = Z P2.CompiledCode
readType t | T.unpack (T.take 1 t) == "L" = L (P.constructQualifiedName $ T.drop 1 (T.dropEnd 1 t)) P2.CompiledCode
readType t  = UnsupportedType P2.CompiledCode

getTypeName :: TypeInfo -> (P.QualifiedName,P2.SourcePos')
getTypeName (Local (P2.NewClazz2 pos _ nm _ _ _)) = (nm,P2.SourcePos' pos)
getTypeName (Path ClassDescriptor {..}) = (P.constructQualifiedName name,P2.CompiledCode)

getTypeParent :: TypeInfo -> (P.QualifiedName,P2.SourcePos')
getTypeParent (Local (P2.NewClazz2 _ _ _ (P2.NewExtends pos nm) _ _)) = (nm,P2.SourcePos' pos)
getTypeParent (Local (P2.NewClazz2 pos _ _ P2.ExtendsObject _ _)) = (P.createQNameObject, P2.SourcePos' pos)
getTypeParent (Path ClassDescriptor {..}) = if T.length parent == 0
  then (P.createQNameObject,P2.CompiledCode)
  else (P.constructQualifiedName parent,P2.CompiledCode)

getFieldType :: TypeInfo -> P.SimpleName -> Maybe Type
getFieldType (Local (P2.NewClazz2 _ _ _ _ fields _)) nm =
  let maybeMatchingField = List.find (\(P2.NewField _ _ _ fieldNm) -> nm == fieldNm) fields
  in
    fmap (\(P2.NewField pos tp _ _) -> L tp (P2.SourcePos' pos)) maybeMatchingField
getFieldType (Path ClassDescriptor {..}) nm =
  let maybeMatchingField = List.find (\Field {..} -> showt nm == fname) fields
  in
    fmap (\Field {..} -> readType ftype) maybeMatchingField

getMethodType :: TypeInfo -> ClassPathSignature -> ExceptT [P2.TypeError] (StateT ClassData IO) (Maybe MethodInvocation)
getMethodType (Local (P2.NewClazz2 _ _ _ _ _ methods)) signature = do
  candidateMethods <- filterCandidateMethods1 methods signature
  sortedMethodList <- sortByM methodSpecificitySorter candidateMethods
  if null sortedMethodList
    then return Nothing
    else return $ Just ((\(P2.NewMethod pos _ _ tp sig _) ->
      NewMethodInvocation (L tp (P2.SourcePos' pos)) (mapSignatureToClassPathSignature sig))
      (List.head sortedMethodList))
getMethodType (Path ClassDescriptor {..}) signature = do
  candidateMethods <- filterCandidateMethods2 methods signature
  sortedMethodList <- sortByM methodSpecificitySorter2 candidateMethods
  if null sortedMethodList
    then return Nothing
    else return $ Just
      (let method = List.head sortedMethodList in
      NewMethodInvocation (mapMethodToType method) (mapMethodToSignature method))

getStaticMethodType :: TypeInfo -> ClassPathSignature -> ExceptT [P2.TypeError] (StateT ClassData IO) (Maybe MethodInvocation)
getStaticMethodType (Local (P2.NewClazz2 _ _ _ _ _ methods)) signature = do
  let staticMethods = List.filter (\P2.NewMethod {} -> False) methods
  candidateMethods <- filterCandidateMethods1 staticMethods signature
  sortedMethodList <- sortByM methodSpecificitySorter candidateMethods
  if null sortedMethodList
    then return Nothing
    else return $ Just ((\(P2.NewMethod pos _ _ tp sig _) ->
      NewMethodInvocation (L tp (P2.SourcePos' pos)) (mapSignatureToClassPathSignature sig))
      (List.head sortedMethodList))
getStaticMethodType (Path ClassDescriptor {..}) signature = do
  let staticMethods = List.filter (\(Method _ _ accessFlags) -> (accessFlags .|. 0x0008) > 0) methods
  candidateMethods <- filterCandidateMethods2 staticMethods signature
  sortedMethodList <- sortByM methodSpecificitySorter2 candidateMethods
  if null sortedMethodList
    then return Nothing
    else return $ Just
      (let method = List.head sortedMethodList in
      NewMethodInvocation (mapMethodToType method) (mapMethodToSignature method))

filterCandidateMethods1 :: [P2.Method] -> ClassPathSignature -> ExceptT [P2.TypeError] (StateT ClassData IO) [P2.Method]
filterCandidateMethods1 methods signature@(ClassPathSignature searchName searchParams) = do
  let candidateMatchingMethods = List.filter (\(P2.NewMethod _ nm _ _ _ _) -> P.deconstructSimpleName nm == searchName) methods
  let candidateMatchingMethods2 = List.filter (\(P2.NewMethod _ _ p _ _ _) -> length p == length searchParams) candidateMatchingMethods
  filterM (\(P2.NewMethod _ _ ps _ _ _) ->
      areParametersInvocationCompatible (fmap getBoxedType searchParams) (fmap mapParameterToType ps)) candidateMatchingMethods2

filterCandidateMethods2 :: [Method] -> ClassPathSignature -> ExceptT [P2.TypeError] (StateT ClassData IO) [Method]
filterCandidateMethods2 methods signature@(ClassPathSignature searchName searchParams) = do
  let candidateMatchingMethods = List.filter (\Method {..} -> mname == searchName) methods
  let candidateMatchingMethods2 = List.filter (\Method {..} -> descriptorParamCount mdescriptor == length searchParams) candidateMatchingMethods
  filterM (areParametersInvocationCompatible (fmap getBoxedType searchParams) . mapMethodToParamTypeList) candidateMatchingMethods2

areParametersInvocationCompatible :: [(P.QualifiedName,P2.SourcePos')] -> [Type] -> ExceptT [P2.TypeError] (StateT ClassData IO) Bool
areParametersInvocationCompatible sigParamTypes candidateParams =
  foldM (\r (ptp, candidatetp) ->
    (r &&) <$> isTypeInvocationCompatible ptp candidatetp) True (zip sigParamTypes candidateParams)

areParametersInvocationCompatible2 :: [P2.Parameter] -> [P2.Parameter] -> ExceptT [P2.TypeError] (StateT ClassData IO) Bool
areParametersInvocationCompatible2 sigParams candidateParams =
  areParametersInvocationCompatible
    (fmap (\(P2.NewParameter pos tp _) -> (tp, P2.SourcePos' pos)) sigParams)
    (fmap (\(P2.NewParameter pos tp _) -> L tp (P2.SourcePos' pos)) candidateParams)

isTypeInvocationCompatible :: (P.QualifiedName, P2.SourcePos') -> Type -> ExceptT [P2.TypeError] (StateT ClassData IO) Bool
isTypeInvocationCompatible _ (UnsupportedType _) = return False
isTypeInvocationCompatible baseType (I sp) = isSubtypeOfE baseType (P.createQNameInteger, sp)
isTypeInvocationCompatible baseType (Z sp) = isSubtypeOfE baseType (P.createQNameBoolean, sp)
isTypeInvocationCompatible baseType (L qn sp) = isSubtypeOfE baseType (qn,sp)

methodSpecificitySorter :: P2.Method -> P2.Method -> ExceptT [P2.TypeError] (StateT ClassData IO) Ordering
methodSpecificitySorter (P2.NewMethod _ _ m1params _ _ _) (P2.NewMethod _ _ m2params _ _ _) = do
  b <- areParametersInvocationCompatible2 m1params m2params
  return $ if b then LT else GT

methodSpecificitySorter2 :: Method -> Method -> ExceptT [P2.TypeError] (StateT ClassData IO) Ordering
methodSpecificitySorter2 method1 method2 = do
  let m1params = mapMethodToParamTypeList method1
  let m2params = mapMethodToParamTypeList method2
  b <- areParametersInvocationCompatible (fmap getBoxedType m1params) m2params
  return $ if b then LT else GT

mapSignatureToClassPathSignature :: P2.Signature -> ClassPathSignature
mapSignatureToClassPathSignature (P2.Signature sn params) =
  ClassPathSignature (P.deconstructSimpleName sn) (fmap qualifiedNameToType params)

qualifiedNameToType :: (P.QualifiedName,SourcePos) -> Type
qualifiedNameToType (qn,pos) = L qn (P2.SourcePos' pos)

descriptorParamCount :: T.Text -> Int
descriptorParamCount descriptor =
  let (paramTypes,_) = parseMethodDescriptor descriptor
  in
    length paramTypes

getBoxedType :: Type -> (P.QualifiedName,P2.SourcePos')
getBoxedType (I sp) = (P.createQNameInteger, sp)
getBoxedType (Z sp) = (P.createQNameBoolean, sp)
getBoxedType tp@(L qn sp) = (qn,sp)
getBoxedType (UnsupportedType _) = undefined

getUnboxedType :: Type -> Type
getUnboxedType (L qn sp) | qn == P.createQNameBoolean = Z sp
                         | qn == P.createQNameInteger = I sp
getUnboxedType t = t

mapMethodToSignature :: Method -> ClassPathSignature
mapMethodToSignature method@Method {..} =
  let (paramTypes,_) = parseMethodDescriptor mdescriptor
  in
    ClassPathSignature mname paramTypes

mapMethodToParamTypeList :: Method -> [Type]
mapMethodToParamTypeList Method {..} =
  let (paramTypes,_) = parseMethodDescriptor mdescriptor
  in
    paramTypes

mapMethodToType :: Method -> Type
mapMethodToType Method {..} =
  let (_,returnType) = parseMethodDescriptor mdescriptor
  in
    returnType

parseMethodDescriptor :: T.Text -> ([Type],Type)
parseMethodDescriptor t =
  let eitherResult = runParser parseMethodDescriptor' () (T.unpack t) (T.unpack t)
  in
    case eitherResult of
      Left e -> trace ("Parse descriptor failure: "++T.unpack t++show e) undefined
      Right r -> r

parseMethodDescriptor' = do
  char '('
  paramTypes <- manyTill (parsePrimitiveType <|> parseReferenceType) (char ')')
  returnType <- parsePrimitiveType <|> parseReferenceType
  return (paramTypes,returnType)

parsePrimitiveType = do
  c <- char 'I' <|> char 'Z' <|> char 'V' <|> char 'B' <|> char 'C' <|> char 'D' <|> char 'F' <|> char 'J' <|> char 'S' <|> char '['
  return $ case c of
    'I' -> I P2.CompiledCode
    'Z' -> Z P2.CompiledCode
    _ -> UnsupportedType P2.CompiledCode

parseReferenceType = do
  char 'L'
  s <-manyTill anyChar (char ';')
  return $ L (P.constructQualifiedName (T.pack s)) P2.CompiledCode

mapParameterToType :: P2.Parameter -> Type
mapParameterToType (P2.NewParameter pos tp _) = L tp (P2.SourcePos' pos)

getClassTypeInfoE :: (P.QualifiedName,P2.SourcePos') -> ExceptT [P2.TypeError] (StateT ClassData IO) TypeInfo
getClassTypeInfoE (tp,pos) = do
  (classPath, classMap) <- lift get
  if Map.member tp classMap
    then case fmap Local (classMap Map.!? tp) of Just a -> return a; Nothing -> throwE [P2.TypeError ("Undefined type: "++T.unpack (showt tp)) pos]
    else do
      (maybecd,classPath') <- lift . lift $ runStateT (getClass (showt tp)) classPath
      lift $ put (classPath',classMap)
      case fmap Path maybecd of Just cd -> return cd; Nothing -> throwE [P2.TypeError ("Undefined type: "++T.unpack (showt tp)) pos]

getClassTypeInfo :: P.QualifiedName -> StateT ClassData IO (Either T.Text TypeInfo)
getClassTypeInfo tp  = do
  (classPath, classMap) <- get
  if Map.member tp classMap
    then return $ case fmap Local (classMap Map.!? tp) of Just a -> Right a; Nothing -> Left (showt tp)
    else do
      (maybecd,classPath') <- lift $ runStateT (getClass (showt tp)) classPath
      put (classPath',classMap)
      return $ case fmap Path maybecd of Just a -> Right a; Nothing -> Left (showt tp)

getClassTypeInfo' :: Either T.Text P.QualifiedName -> StateT ClassData IO (Either T.Text TypeInfo)
getClassTypeInfo' eTp  = case eTp of
  Left txt -> return $ Left txt
  Right tp -> getClassTypeInfo tp

isSubtypeOfE :: (P.QualifiedName,P2.SourcePos')  -> (P.QualifiedName,P2.SourcePos') -> ExceptT [P2.TypeError] (StateT ClassData IO) Bool
isSubtypeOfE childQn parentQn = do
  childType <- getClassTypeInfoE childQn
  parentType <- getClassTypeInfoE parentQn
  if (fst (getTypeName childType) == fst (getTypeName parentType)) || (fst (getTypeParent childType) == fst (getTypeName parentType))
    then return True
    else do
      let childParentQName = getTypeParent childType
      if fst childParentQName == fst (getTypeName childType) -- Only java/lang/Object has itself as a parent
        then return False
        else do
          isSubtypeOfE childParentQName parentQn

{--
isSubtypeOfE' :: Either T.Text TypeInfo -> Either [P2.TypeError] TypeInfo -> ExceptT [P2.TypeError] (StateT ClassData IO) Bool
isSubtypeOfE' eChildType eParentType = do
  case eChildType of
    Left txt -> throwE txt
    Right childType -> case eParentType of
      Left txt -> throwE txt
      Right parentType -> isSubtypeOfE (getTypeName childType) (getTypeName parentType)
-}

isSubtypeOf' :: TypeInfo -> TypeInfo -> ExceptT [P2.TypeError] (StateT ClassData IO) Bool
isSubtypeOf' childType parentType = isSubtypeOfE (getTypeName childType) (getTypeName parentType)

{--
isSubtypeOf :: Either T.Text TypeInfo -> Either T.Text TypeInfo -> ExceptT [P2.TypeError] (StateT ClassData IO) Bool
isSubtypeOf eChildType eParentType = do
  case eChildType of
    Left txt -> return $ Left txt
    Right childType -> case eParentType of
      Left txt -> return $ Left txt
      Right parentType -> isSubtypeOf' childType parentType
-}

isValidClass :: ClassData -> P.QualifiedName -> Bool
isValidClass (classPath,classMap) tp = Map.member tp classMap || hasClass classPath (toText (showb tp))

isTypeBoolean :: Type -> Bool
isTypeBoolean (Z _) = True
isTypeBoolean _ = False

isTypeInteger :: Type -> Bool
isTypeInteger (I _) = True
isTypeInteger _ = False

getSupertypeSet :: P.QualifiedName -> ExceptT [P2.TypeError] (StateT ClassData IO) [P.QualifiedName]
getSupertypeSet tp = do
  unfoldrM (\qn -> if qn /= P.createQNameObject then fmap (\ti -> Just (qn, fst (getTypeParent ti))) (getClassTypeInfoE (qn,P2.CompiledCode)) else return Nothing) tp

