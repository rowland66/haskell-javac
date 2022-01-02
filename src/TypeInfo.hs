{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

module TypeInfo
( TypeInfo
, getClassTypeInfo
, getClassTypeInfo'
, isSubtypeOf
, getFieldType
, getTypeName
, getTypeParent
, getMethodType
, getStaticMethodType
, isValidClass
, getBoxedType
) where

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.List as List
import Control.Monad.Trans.Except
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

{-- TypeInfo provides type information. A Local TypeInfo provides type information for types defined in the
    code being compiled. Path TypeInfo provides type information for types found on the classspath in compiled
    class files -}
data TypeInfo = Local P2.Clazz2 | Path ClassDescriptor

type ClassData = (ClassPath,P2.LocalClasses)

init' = T.pack "<init>"
object = T.pack "java/lang/Object"
rparens = T.pack ")"
semi = T.pack ";"

getTypeName :: TypeInfo -> P.QualifiedName
getTypeName (Local (P2.NewClazz2 _ _ nm _ _ _)) = nm
getTypeName (Path ClassDescriptor {..}) = P.constructQualifiedName name

getTypeParent :: TypeInfo -> P.QualifiedName
getTypeParent (Local (P2.NewClazz2 _ _ _ (P2.NewExtends _ nm) _ _)) = nm
getTypeParent (Local (P2.NewClazz2 _ _ _ P2.ExtendsObject _ _)) = P.createQNameObject
getTypeParent (Path ClassDescriptor {..}) = if T.length parent == 0 then P.createQNameObject else P.constructQualifiedName parent

getFieldType :: TypeInfo -> P.SimpleName -> Maybe P2.Type
getFieldType (Local (P2.NewClazz2 _ _ _ _ fields _)) nm =
  let maybeMatchingField = List.find (\(P2.NewField _ _ _ fieldNm) -> nm == fieldNm) fields
  in
    fmap (\(P2.NewField _ tp _ _) -> P2.L tp) maybeMatchingField
getFieldType (Path ClassDescriptor {..}) nm =
  let maybeMatchingField = List.find (\Field {..} -> showt nm == fname) fields
  in
    fmap (\Field {..} -> P2.readType ftype) maybeMatchingField

getMethodType :: TypeInfo -> P2.Signature -> StateT ClassData IO (Maybe P2.MethodInvocation)
getMethodType (Local (P2.NewClazz2 _ _ _ _ _ methods)) signature = do
  candidateMethods <- filterCandidateMethods1 methods signature
  sortedMethodList <- sortByM methodSpecificitySorter candidateMethods
  if null sortedMethodList
    then return Nothing
    else return $ Just ((\(P2.NewMethod _ _ _ tp sig _) -> P2.NewMethodInvocation (P2.L tp) sig) (List.head sortedMethodList))
getMethodType (Path ClassDescriptor {..}) signature = do
  candidateMethods <- filterCandidateMethods2 methods signature
  sortedMethodList <- sortByM methodSpecificitySorter2 candidateMethods
  if null sortedMethodList
    then return Nothing
    else return $ Just
      (let method = List.head sortedMethodList in
      P2.NewMethodInvocation (mapMethodToType method) (mapMethodToSignature method))

getStaticMethodType :: TypeInfo -> P2.Signature -> StateT ClassData IO (Maybe P2.MethodInvocation)
getStaticMethodType (Local (P2.NewClazz2 _ _ _ _ _ methods)) signature = do
  let staticMethods = List.filter (\P2.NewMethod {} -> False) methods
  candidateMethods <- filterCandidateMethods1 staticMethods signature
  sortedMethodList <- sortByM methodSpecificitySorter candidateMethods
  if null sortedMethodList
    then return Nothing
    else return $ Just ((\(P2.NewMethod _ _ _ tp sig _) -> P2.NewMethodInvocation (P2.L tp) sig) (List.head sortedMethodList))
getStaticMethodType (Path ClassDescriptor {..}) signature = do
  let staticMethods = List.filter (\(Method _ _ accessFlags) -> (accessFlags .|. 0x0008) > 0) methods
  candidateMethods <- filterCandidateMethods2 staticMethods signature
  sortedMethodList <- sortByM methodSpecificitySorter2 candidateMethods
  if null sortedMethodList
    then return Nothing
    else return $ Just
      (let method = List.head sortedMethodList in
      P2.NewMethodInvocation (mapMethodToType method) (mapMethodToSignature method))

filterCandidateMethods1 :: [P2.Method] -> P2.Signature -> StateT ClassData IO [P2.Method]
filterCandidateMethods1 methods signature@(P2.Signature searchName searchParams) = do
  let candidateMatchingMethods = List.filter (\(P2.NewMethod _ nm _ _ _ _) -> nm == searchName) methods
  let candidateMatchingMethods2 = List.filter (\(P2.NewMethod _ _ p _ _ _) -> length p == length searchParams) candidateMatchingMethods
  filterM (\(P2.NewMethod _ _ ps _ _ _) ->
    fmap (\case Right b -> b; Left _ -> False)
      (runExceptT (areParametersInvocationCompatible searchParams (fmap mapParameterToType ps)))) candidateMatchingMethods2

filterCandidateMethods2 :: [Method] -> P2.Signature -> StateT ClassData IO [Method]
filterCandidateMethods2 methods signature@(P2.Signature searchName searchParams) = do
  let candidateMatchingMethods = List.filter (\Method {..} -> mname == P.deconstructSimpleName searchName) methods
  let candidateMatchingMethods2 = List.filter (\Method {..} -> descriptorParamCount mdescriptor == length searchParams) candidateMatchingMethods
  filterM (fmap (\case Right b -> b; Left _ -> False) .
    runExceptT . areParametersInvocationCompatible searchParams . mapMethodToParamTypeList) candidateMatchingMethods2

areParametersInvocationCompatible :: [P2.Type] -> [P2.Type] -> ExceptT T.Text (StateT ClassData IO) Bool
areParametersInvocationCompatible sigParamTypes candidateParams =
  foldM (\r (ptp, candidatetp) ->
    (r &&) <$> isTypeInvocationCompatible ptp candidatetp) True (zip sigParamTypes candidateParams)

areParametersInvocationCompatible2 :: [P2.Parameter] -> [P2.Parameter] -> ExceptT T.Text (StateT ClassData IO) Bool
areParametersInvocationCompatible2 sigParams candidateParams =
  areParametersInvocationCompatible
    (fmap (\(P2.NewParameter _ tp _) -> P2.L tp) sigParams)
    (fmap (\(P2.NewParameter _ tp _) -> P2.L tp) candidateParams)

isTypeInvocationCompatible :: P2.Type -> P2.Type -> ExceptT T.Text (StateT ClassData IO) Bool
isTypeInvocationCompatible _ (P2.Unsupported _) = return False
isTypeInvocationCompatible (P2.Unsupported _) _ = return False
isTypeInvocationCompatible baseType candidateType = isSubtypeOfE (getBoxedType baseType) (getBoxedType candidateType)



methodSpecificitySorter :: P2.Method -> P2.Method -> StateT ClassData IO Ordering
methodSpecificitySorter (P2.NewMethod _ _ m1params _ _ _) (P2.NewMethod _ _ m2params _ _ _) = do
  eitherResult <- runExceptT $ areParametersInvocationCompatible2 m1params m2params
  return $ case eitherResult of
    Left txt -> undefined -- This should never happen as types have been resoved already
    Right b -> if b then LT else GT

methodSpecificitySorter2 :: Method -> Method -> StateT ClassData IO Ordering
methodSpecificitySorter2 method1 method2 = do
  let m1params = mapMethodToParamTypeList method1
  let m2params = mapMethodToParamTypeList method2
  eitherResult <- runExceptT $ areParametersInvocationCompatible m1params m2params
  return $ case eitherResult of
    Left txt -> undefined -- This should never happen as types have been resoved already
    Right b -> if b then LT else GT

descriptorParamCount :: T.Text -> Int
descriptorParamCount descriptor =
  let (paramTypes,_) = parseMethodDescriptor descriptor
  in
    length paramTypes

getBoxedType :: P2.Type -> P.QualifiedName
getBoxedType P2.I = P.createQNameInteger
getBoxedType P2.Z = P.createQNameBoolean
getBoxedType (P2.L qn) = qn
getBoxedType (P2.Unsupported t) = trace ("Unsupport boxing"++show t) undefined

mapMethodToSignature :: Method -> P2.Signature
mapMethodToSignature method@Method {..} =
  let (paramTypes,_) = parseMethodDescriptor mdescriptor
  in
    P2.Signature (P.constructSimpleName mname) paramTypes

mapMethodToParamTypeList :: Method -> [P2.Type]
mapMethodToParamTypeList Method {..} =
  let (paramTypes,_) = parseMethodDescriptor mdescriptor
  in
    paramTypes

mapMethodToType :: Method -> P2.Type
mapMethodToType Method {..} =
  let (_,returnType) = parseMethodDescriptor mdescriptor
  in
    returnType

parseMethodDescriptor :: T.Text -> ([P2.Type],P2.Type)
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
    'I' -> P2.I
    'Z' -> P2.Z
    _ -> P2.Unsupported (T.pack [c])

parseReferenceType = do
  char 'L'
  s <-manyTill anyChar (char ';')
  return $ P2.L $ P.constructQualifiedName (T.pack s)

mapParameterToType :: P2.Parameter -> P2.Type
mapParameterToType (P2.NewParameter _ tp _) = P2.L tp

getClassTypeInfoE :: P.QualifiedName -> ExceptT T.Text (StateT ClassData IO) TypeInfo
getClassTypeInfoE tp  = do
  (classPath, classMap) <- lift get
  if Map.member tp classMap
    then case fmap Local (classMap Map.!? tp) of Just a -> return a; Nothing -> throwE (showt tp)
    else do
      (maybecd,classPath') <- lift . lift $ runStateT (getClass (showt tp)) classPath
      lift $ put (classPath',classMap)
      case fmap Path maybecd of Just cd -> return cd; Nothing -> throwE (showt tp)

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

isSubtypeOfE :: P.QualifiedName  -> P.QualifiedName  -> ExceptT T.Text (StateT ClassData IO) Bool
isSubtypeOfE childQn parentQn = do
  childType <- getClassTypeInfoE childQn
  parentType <- getClassTypeInfoE parentQn
  if (getTypeName childType == getTypeName parentType) || (getTypeParent childType == getTypeName parentType)
    then return True
    else do
      let childParentQName = getTypeParent childType
      if childParentQName == getTypeName childType -- Only java/lang/Object has itself as a parent
        then return False
        else do
          isSubtypeOfE childParentQName parentQn

isSubtypeOfE' :: Either T.Text TypeInfo -> Either T.Text TypeInfo -> ExceptT T.Text (StateT ClassData IO) Bool
isSubtypeOfE' eChildType eParentType = do
  case eChildType of
    Left txt -> throwE txt
    Right childType -> case eParentType of
      Left txt -> throwE txt
      Right parentType -> isSubtypeOfE (getTypeName childType) (getTypeName parentType)

isSubtypeOf' :: TypeInfo -> TypeInfo -> StateT ClassData IO (Either T.Text Bool)
isSubtypeOf' childType parentType = do
  if (getTypeName childType == getTypeName parentType) || (getTypeParent childType == getTypeName parentType)
    then return $ Right True
    else do
      let childParentQName = getTypeParent childType
      if childParentQName == getTypeName childType
        then return $ Right False
        else do
          eitherChildParent <- getClassTypeInfo childParentQName
          join <$> mapM (`isSubtypeOf'` parentType) eitherChildParent

isSubtypeOf :: Either T.Text TypeInfo -> Either T.Text TypeInfo -> StateT ClassData IO (Either T.Text Bool)
isSubtypeOf eChildType eParentType = do
  case eChildType of
    Left txt -> return $ Left txt
    Right childType -> case eParentType of
      Left txt -> return $ Left txt
      Right parentType -> isSubtypeOf' childType parentType

isValidClass :: ClassData -> P.QualifiedName -> Bool
isValidClass (classPath,classMap) tp = Map.member tp classMap || hasClass classPath (toText (showb tp))
