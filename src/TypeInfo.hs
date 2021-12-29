{-# LANGUAGE RecordWildCards #-}

module TypeInfo
( TypeInfo
, getClassTypeInfo
, getClassTypeInfo'
, isSubtypeOf
, isSubtypeOf'
, hasConstructorWithSignature
, hasConstructorWithSignature'
, getFieldType
, getTypeParent
, getMethodType
, isValidClass
) where

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.List as List
import ClassPath (ClassPath, ClassDescriptor(..), getClass, Field (..), Method (..), hasClass)
import qualified Parser2 as P2
import qualified Parser as P
import TextShow (toText, showb, showt)
import Control.Monad.Extra ( foldM, ifM, join )
import Data.Tuple.Sequence ( SequenceT(sequenceT) )
import Data.List (foldl')
import Debug.Trace ( trace )

data TypeInfo = Local P2.Clazz2 | Path ClassDescriptor

type ClassData = (ClassPath,P2.LocalClasses)

init' = T.pack "<init>"
object = T.pack "java/lang/Object"
rparens = T.pack ")"
semi = T.pack ";"

getTypeName :: TypeInfo -> P.QualifiedName
getTypeName (Local (P2.NewClazz2 _ _ nm _ _ _ _)) = nm
getTypeName (Path ClassDescriptor {..}) = P.constructQualifiedName name

getTypeParent :: TypeInfo -> P.QualifiedName
getTypeParent (Local (P2.NewClazz2 _ _ _ (P2.NewExtends _ nm) _ _ _)) = nm
getTypeParent (Local (P2.NewClazz2 _ _ _ P2.ExtendsObject _ _ _)) = P.createQNameObject
getTypeParent (Path ClassDescriptor {..}) = P.constructQualifiedName parent

getTypeConstructors :: TypeInfo -> [P2.Signature]
getTypeConstructors (Local (P2.NewClazz2 _ _ _ _ _ constructors _)) =
  fmap (\(P2.NewConstructor _ _ sig _ _) -> sig) constructors
getTypeConstructors (Path ClassDescriptor {..}) =
  let constructors = List.filter (\Method {..} -> mname == init') methods
  in
    fmap mapMethodToSignature constructors

getFieldType :: TypeInfo -> P.SimpleName -> Maybe P.QualifiedName
getFieldType (Local (P2.NewClazz2 _ _ _ _ fields _ _)) nm =
  let maybeMatchingField = List.find (\(P2.NewField _ _ _ fieldNm) -> nm == fieldNm) fields
  in
    fmap (\(P2.NewField _ tp _ _) -> tp) maybeMatchingField
getFieldType (Path ClassDescriptor {..}) nm =
  let maybeMatchingField = List.find (\Field {..} -> showt nm == fname) fields
  in
    fmap (\Field {..} -> P.constructQualifiedName ftype) maybeMatchingField

getMethodType :: TypeInfo -> P2.Signature -> Maybe P.QualifiedName
getMethodType (Local (P2.NewClazz2 _ _ _ _ _ _ methods)) signature =
  let maybeMatchingMethod = List.find (\(P2.NewMethod _ _ _ _ sig _) -> sig == signature) methods
  in
    fmap (\(P2.NewMethod _ _ _ tp _ _) -> tp) maybeMatchingMethod
getMethodType (Path ClassDescriptor {..}) signature =
  let maybeMatchingMethod = List.find (\method -> mapMethodToSignature method == signature) methods
  in
    fmap mapMethodToType maybeMatchingMethod

mapMethodToSignature :: Method -> P2.Signature
mapMethodToSignature Method {..} =
  let paramTxt = T.drop 1 $ T.dropEnd 1 $ fst (T.breakOnEnd rparens mdescriptor)
      paramList = fmap (T.drop 1) (filter (/= T.pack "") (T.splitOn semi paramTxt))
      paramQnList = fmap P.constructQualifiedName paramList
  in
    P2.Signature (P.constructSimpleName mname) paramQnList

mapMethodToType :: Method -> P.QualifiedName
mapMethodToType Method {..} =
  let rtrnTxt = T.drop 1 $ T.dropEnd 1 $ snd (T.breakOnEnd rparens mdescriptor)
  in
    P.constructQualifiedName rtrnTxt

getClassTypeInfo :: ClassData -> P.QualifiedName -> IO (Either T.Text TypeInfo)
getClassTypeInfo (classPath, classMap) tp  =
  if Map.member tp classMap
    then return $ case fmap Local (classMap Map.!? tp) of Just a -> Right a; Nothing -> Left (showt tp)
    else do
      maybecd <- getClass classPath (showt tp)
      return $ case fmap Path maybecd of Just a -> Right a; Nothing -> Left (showt tp)

getClassTypeInfo' :: ClassData -> Either T.Text P.QualifiedName -> IO (Either T.Text TypeInfo)
getClassTypeInfo' typeData eTp  = case eTp of
  Left txt -> return $ Left txt
  Right tp -> getClassTypeInfo typeData tp

isSubtypeOf :: ClassData -> TypeInfo -> TypeInfo -> IO (Either T.Text Bool)
isSubtypeOf typeData childType parentType = do
  if (getTypeName childType == getTypeName parentType) || (getTypeParent childType == getTypeName parentType)
    then return $ Right True
    else do
      eitherChildParent <- getClassTypeInfo typeData (getTypeParent childType)
      join <$> mapM (\childParent -> isSubtypeOf typeData childParent parentType) eitherChildParent

isSubtypeOf' :: ClassData -> Either T.Text TypeInfo -> Either T.Text TypeInfo -> IO (Either T.Text Bool)
isSubtypeOf' typeData eChildType eParentType = do
  case eChildType of
    Left txt -> return $ Left txt
    Right childType -> case eParentType of
      Left txt -> return $ Left txt
      Right parentType -> isSubtypeOf typeData childType parentType

{-- Does the given class have a constructor with the given signature -}
hasConstructorWithSignature :: ClassData -> TypeInfo -> P2.Signature -> IO (Either T.Text Bool)
hasConstructorWithSignature typeData tp signature = do
  compatibleList <- mapM (isCompatible typeData signature) (getTypeConstructors tp)
  case sequence compatibleList of
    Left txt -> return $ Left txt
    Right bs -> do
      case List.find id bs of
        Just _ -> return $ Right True
        Nothing -> return $ Right False

hasConstructorWithSignature' :: ClassData -> Either T.Text TypeInfo -> P2.Signature -> IO (Either T.Text Bool)
hasConstructorWithSignature' typeData etp signature = do
  case etp of
    Left txt -> return $ Left txt
    Right tp -> hasConstructorWithSignature typeData tp signature

isCompatible :: ClassData -> P2.Signature -> P2.Signature -> IO (Either T.Text Bool)
isCompatible typeData sig1@(P2.Signature nm1 types1) sig2@(P2.Signature nm2 types2)
  | nm1 /= nm2 = return $ Right False
  | length types1 /= length types2 = return $ Right False
  | otherwise = do
  eitherTypeInfoPairs <- mapM (getTypeForPair typeData) (zip types1 types2)
  case sequence eitherTypeInfoPairs of
    Left txt -> return $ Left txt
    Right typeInfoPairs -> do
      eitherPairsMatch <- mapM (uncurry (isSubtypeOf typeData)) typeInfoPairs
      case sequence eitherPairsMatch of
        Left txt -> return $ Left txt
        Right bs -> return $ Right $ foldl' (&&) True bs

getTypeForPair :: ClassData -> (P.QualifiedName, P.QualifiedName) -> IO (Either T.Text (TypeInfo, TypeInfo))
getTypeForPair typeData (f,s) = do
  maybeft <- getClassTypeInfo typeData f
  maybest <- getClassTypeInfo typeData s
  return $ sequenceT (maybeft, maybest)

isValidClass :: ClassData -> P.QualifiedName -> IO Bool
isValidClass (classPath,classMap) tp = (Map.member tp classMap ||) <$> hasClass classPath (toText (showb tp))
