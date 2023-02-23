{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}

module TypeInfo
( TypeInfo(..)
, TypeInfo_
, ClassAccessFlags(..)
, FieldDeclaration(..)
, FieldAttributes(..)
, MethodSignature(..)
, MethodAttributes(..)
, MethodDeclaration(..)
, TypeParamEnvironment
, Type(..)
, getClassTypeInfo
, getClassTypeInfo'
, getTypeName
, getTypeParameters
, getTypeParent
, getTypeFields
, getTypeMethods
, getTypeAccessFlags
, getTypeFieldDeclaration
, getTypePotentiallyApplicableMethods
, isTypeSupported
, isTypeParameterized
, getFieldName
, getFieldType
, getFieldAttributes
, getFieldClassName
, getMethodName
, getMethodType
, getMethodParams
, getMethodAttributes
, getMethodSignature
, getMethodClassName
, getErasedTypeName
, getErasedMethodSignature
, eraseParameterizedType
, getErasedType
, getTypeImplements
, getTypeClassReferenceType
) where

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as S
import qualified Data.Vector as V
import Control.Monad.Loops (unfoldrM)
import Control.Monad.Trans.Except ( ExceptT, runExceptT, throwE )
import Control.Monad.ListM (sortByM)
import Data.Bits
import Data.Word
import ClassPath as CP
import TextShow (toText, showb, showt)
import Control.Monad.Extra ( foldM, ifM, join, filterM )
import Data.Tuple.Sequence ( SequenceT(sequenceT) )
import Data.List (foldl')
import Debug.Trace ( trace )
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT,get,put,runStateT)
import qualified Parser as P
import qualified Parser2 as P2

import qualified Data.Tuple.Extra as Data.Bifunctor
import qualified Data.FlagSet as FS
import TypeValidator
import TypeCheckerTypes

{-- TypeInfo provides type information. A Local TypeInfo provides type information for types defined in the
    code being compiled. Path TypeInfo provides type information for types found on the classspath in compiled
    class files. 
-}
data TypeInfo = forall a. (TypeInfo_ a) => TypeInfo a

instance Show TypeInfo where
  show (TypeInfo a) = show (getTypeName a)

class TypeInfo_ t where
  getTypeName :: t -> TypeCheckerValidTypeQualifiedNameWrapper
  getTypeParent :: t -> TypeCheckerClassReferenceTypeWrapper
  getTypeImplements :: t -> [TypeCheckerClassReferenceTypeWrapper]
  getTypeFields :: t -> [FieldDeclaration]
  getTypeMethods :: t -> [MethodDeclaration]
  getTypeAccessFlags :: t -> ClassAccessFlags
  getTypeParameters :: t -> [TypeCheckerTypeParameter]
  getTypeFieldDeclaration :: t -> P.SimpleName -> Maybe FieldDeclaration
  getTypeFieldDeclaration ti nm =
    List.find (\(FieldDeclaration f) -> nm == getFieldName f) (getTypeFields ti)

  {-- Get a list of method declartions that are potentially applicable to the provided MethodSignature -}
  getTypePotentiallyApplicableMethods :: t -> MethodSignature -> StateT ValidTypeClassData IO [MethodDeclaration]
  getTypePotentiallyApplicableMethods ti signature@(MethodSignature searchName searchParams) = do
    let candidateMatchingMethods = List.filter 
          (\(MethodDeclaration m) ->
              P.deconstructSimpleName (getMethodName m) == searchName)
          (getTypeMethods ti)
    let returnList = List.filter (\(MethodDeclaration m) ->
          length (getMethodParams m) == length searchParams) candidateMatchingMethods
    return returnList


instance TypeInfo_ ValidTypeClazz where
  getTypeName ValidTypeClazz {..} = vcName
  getTypeParent ValidTypeClazz {..} = fst vcParent
  getTypeImplements _ = []
  getTypeFields ValidTypeClazz {..} = fmap FieldDeclaration vcFields
  getTypeMethods ValidTypeClazz {..} = fmap MethodDeclaration vcMethods
  getTypeAccessFlags ValidTypeClazz {..} = ClassAccessFlags { caAbstract = P.CAbstract `elem` vcAccessFlags
                                                            , caInterface = P.CInterface `elem` vcAccessFlags
                                                            , caPublic = P.CPublic `elem` vcAccessFlags}
  getTypeParameters _ = []

instance TypeInfo_ ClassDescriptor where
  getTypeName ClassDescriptor {..} = name
  getTypeParent ClassDescriptor {..} = parent
  getTypeImplements ClassDescriptor {..} = S.toList interfaceClasses
  getTypeFields ClassDescriptor {..} = fmap FieldDeclaration fields
  getTypeMethods ClassDescriptor {..} = fmap MethodDeclaration (filter concreteMethod methods)
  getTypeAccessFlags ClassDescriptor {..} = ClassAccessFlags { caAbstract = FS.match accessFlags CP.cAbstractMaskedValue
                                                             , caInterface = FS.match accessFlags CP.cInterfaceMaskedValue
                                                             , caPublic = FS.match accessFlags CP.cPublicMaskedValue
                                                             }
  getTypeParameters ClassDescriptor {..} = V.toList typeParameters

concreteMethod :: CP.Method -> Bool
concreteMethod CP.Method {..} = not (FS.match maccessFlags CP.mSyncheticMaskedValue) && not (FS.match maccessFlags CP.mBridgeMaskedValue)

class Field_ f where
  getFieldName :: f -> P.SimpleName
  getFieldType :: f -> Type
  getFieldAttributes :: f -> FieldAttributes
  getFieldClassName :: f -> TypeCheckerValidTypeQualifiedNameWrapper

instance Field_ ValidTypeField where
  getFieldName ValidTypeField {..} = fst vfName
  getFieldType ValidTypeField {..} = L vfType
  getFieldAttributes ValidTypeField {..} = FieldAttributes { faStatic=False }
  getFieldClassName ValidTypeField{..} = vfClassName

instance Field_ Field where
  getFieldName CP.Field {..} = P.constructSimpleName fname
  getFieldType CP.Field {..} = convertClassPathType ftype
  getFieldAttributes CP.Field {..} = FieldAttributes { faStatic=FS.match faccessFlags CP.fStaticMaskedValue }
  getFieldClassName CP.Field{..} = fcClassName

class Method_ m where
  getMethodName :: m -> P.SimpleName
  getMethodType :: m -> Type
  getMethodParams :: m -> [Type]
  getMethodAttributes :: m -> MethodAttributes
  getMethodSignature :: m -> MethodSignature
  getMethodClassName :: m -> TypeCheckerValidTypeQualifiedNameWrapper

instance Method_ ValidTypeMethod where
  getMethodName ValidTypeMethod {..} = fst vmName
  getMethodType ValidTypeMethod {..} = L vmType
  getMethodParams ValidTypeMethod {..} = fmap (L . vpType) (V.toList vmParams)
  getMethodAttributes ValidTypeMethod {..} = MethodAttributes { maStatic=False
                                                              , maAbstract=case vmMaybeImpl of Just _ -> False; Nothing -> True
                                                              }
  getMethodSignature method@ValidTypeMethod {..} =
    let (SimpleName mname, _) = vmName
    in
      MethodSignature mname (getMethodParams method)
  getMethodClassName ValidTypeMethod{..} = vmClassName

instance Method_ Method where
  getMethodName CP.Method {..} = P.constructSimpleName mname
  getMethodType m = convertClassPathType (mapMethodToResultType m)
  getMethodParams m = fmap convertClassPathType (CP.mapMethodToParamTypeList m)
  getMethodAttributes CP.Method {..} =  MethodAttributes { maStatic=FS.match maccessFlags CP.mStaticMaskedValue
                                                         , maAbstract=FS.match maccessFlags CP.mAbstractMaskedValue
                                                         }
  getMethodSignature method = MethodSignature (mname method) (getMethodParams method)
  getMethodClassName CP.Method{..} = mcClassName

data ClassAccessFlags = ClassAccessFlags { caAbstract :: Bool
                                         , caInterface :: Bool
                                         , caPublic :: Bool
                                         } deriving Show

newtype FieldAttributes = FieldAttributes {faStatic :: Bool} deriving Show

data FieldDeclaration = forall f.(Field_ f) => FieldDeclaration f

type TypeParamEnvironment = Map.Map SimpleName TypeCheckerReferenceTypeWrapper

data MethodSignature = MethodSignature T.Text [Type] deriving Eq

data MethodAttributes = MethodAttributes { maStatic :: Bool
                                         , maAbstract :: Bool
                                         } deriving Show

data MethodDeclaration = forall m.(Show m, Method_ m) => MethodDeclaration m

instance Show MethodDeclaration where
  show (MethodDeclaration a) =
    let isStatic = maStatic (getMethodAttributes a)
        isAbstract = maAbstract (getMethodAttributes a)
        returnType = getMethodType a
        name = getMethodName a
        params = getMethodParams a
    in
      (if isStatic then "static " else "") ++
      (if isAbstract then "abstract " else "") ++
      show returnType ++ " " ++
      show name ++
      ("(" ++ (if null params then "" else List.intercalate "," (fmap show params)) ++ ")")

data Type = I
          | Z
          | U -- Unsupported primitive
          | L !TypeCheckerClassReferenceTypeWrapper
          | T !SimpleName

instance Show Type where
  show I = "I"
  show Z = "Z"
  show U = "Unsupported"
  show (L t) = show t
  show (T v) = show v

instance Eq Type where
  (==) t1 t2 = show t1 == show t2

instance Show MethodSignature where
  show (MethodSignature nm paramTypes) = T.unpack nm++"("++List.intercalate "," (fmap show paramTypes)++")"

convertClassPathType :: ClassPathType -> Type
convertClassPathType cpt | isClassPathTypeBoolean cpt = Z
convertClassPathType cpt | isClassPathTypeInteger cpt = I
convertClassPathType cpt | case getClassPathTypeReference cpt of
                             Just _ -> True
                             Nothing -> False
                         = case getClassPathTypeReference cpt of
                             Just cpcrt -> L cpcrt
                             Nothing -> undefined
convertClassPathType cpt  | case getClassPathTypeVariable cpt of
                              Just _ -> True
                              Nothing -> False
                          = maybe undefined T (getClassPathTypeVariable cpt)
convertClassPathType cpt = trace ("Unsupported ClassPathType: "++show cpt) U

isTypeSupported :: Type -> Bool
isTypeSupported I = True
isTypeSupported Z = True
isTypeSupported U = False
isTypeSupported (L _) = True
isTypeSupported (T _) = True

isTypeParameterized :: Type -> Bool
isTypeParameterized I = False
isTypeParameterized Z = False
isTypeParameterized U = False
isTypeParameterized (L (TypeCheckerClassReferenceTypeWrapper _ (Just _))) = True
isTypeParameterized (L (TypeCheckerClassReferenceTypeWrapper _ Nothing)) = False
isTypeParameterized (T _) = False

getClassTypeInfo :: TypeCheckerClassReferenceTypeWrapper -> StateT ValidTypeClassData IO TypeInfo
getClassTypeInfo (TypeCheckerClassReferenceTypeWrapper vtqnw _) = getClassTypeInfo' vtqnw

getClassTypeInfo' :: TypeCheckerValidTypeQualifiedNameWrapper -> StateT ValidTypeClassData IO TypeInfo
getClassTypeInfo' vtqnw = do
  (classPath, classMap) <- get
  let maybeLocalClass = classMap Map.!? vtqnw
  case maybeLocalClass of
    Just vtc -> return $ TypeInfo vtc
    Nothing -> do
      (classPathType, newClassPath) <- lift $ runStateT (getClassPathValidType vtqnw) classPath
      put (newClassPath, classMap)
      return (TypeInfo classPathType)

getSupertypeSet :: TypeInfo -> StateT ValidTypeClassData IO [TypeInfo]
getSupertypeSet ti = do
  listWithoutObject <- unfoldrM
      (\tiw@(TypeInfo ti') -> if getTypeName ti' == CP.createValidTypeNameObject
                            then return Nothing
                            else Just <$> ((,) tiw <$> getClassTypeInfo (getTypeParent ti')))
      ti
  objectTI <- getClassTypeInfo CP.createValidTypeClassTypeObject
  return $ reverse $ objectTI:listWithoutObject

{--getFieldDeclaration (Path ClassDescriptor {..}) nm =
  let maybeMatchingField = List.find (\CP.Field {..} -> showt nm == fname) fields
  in
    fmap (\CP.Field {..} ->
      let faStatic = FS.match faccessFlags CP.fStaticMaskedValue
      in
        FieldDeclaration (FieldAttributes {..}) (convertClassPathType ftype) fname)
    maybeMatchingField
-}

objectTypeParameterBound :: TypeCheckerTypeBound
objectTypeParameterBound = TypeCheckerClassTypeTypeBound (TypeCheckerClassReferenceTypeWrapper createValidTypeNameObject Nothing) S.empty

getErasedTypeName :: TypeCheckerClassReferenceTypeWrapper -> TypeCheckerValidTypeQualifiedNameWrapper
getErasedTypeName (TypeCheckerClassReferenceTypeWrapper vtqn _) = vtqn

getErasedMethodSignature :: [TypeCheckerTypeParameter] -> MethodDeclaration -> MethodSignature
getErasedMethodSignature typeParams (MethodDeclaration method) = 
  MethodSignature (showt (getMethodName method)) (getErasedMethodParams typeParams (getMethodParams method))

getErasedMethodParams :: [TypeCheckerTypeParameter] -> [Type] -> [Type]
getErasedMethodParams typeParams = fmap (getErasedType typeParams)

getErasedType :: [TypeCheckerTypeParameter] -> Type -> Type
getErasedType _ (L (TypeCheckerClassReferenceTypeWrapper cpvtn maybeTypeArgs)) =
  eraseParameterizedType (TypeCheckerClassReferenceTypeWrapper cpvtn maybeTypeArgs)
getErasedType typeParams (T sn) = eraseTypeVariable typeParams sn
--getErasedType typeParams (A cpt) = eraseRefType typeParams cpt
getErasedType _ cpt = cpt

eraseTypeVariable :: [TypeCheckerTypeParameter] -> SimpleName -> Type
eraseTypeVariable typeParams tv =
  let maybeTypeVariableTypeParam = List.find (\(TypeCheckerTypeParameter sn maybeBound) -> sn == tv) typeParams
  in
    case maybeTypeVariableTypeParam of
      Nothing -> error ("Type variable with no matching type parameter: "++show tv)
      Just (TypeCheckerTypeParameter sn Nothing) -> L createValidTypeClassTypeObject
      Just (TypeCheckerTypeParameter sn (Just (TypeCheckerClassTypeTypeBound classBound _))) -> getErasedType typeParams (L classBound)
      Just (TypeCheckerTypeParameter sn (Just (TypeCheckerTypeVariableTypeBound tvBound))) -> getErasedType typeParams (T tvBound)

eraseParameterizedType :: TypeCheckerClassReferenceTypeWrapper -> Type
eraseParameterizedType (TypeCheckerClassReferenceTypeWrapper validQn _) = L (TypeCheckerClassReferenceTypeWrapper validQn Nothing)

getTypeClassReferenceType :: Type -> TypeCheckerClassReferenceTypeWrapper
getTypeClassReferenceType (L crtw) = crtw
getTypeClassReferenceType t = error ("Unable to convert Type to TypeCheckerClassReference: "++show t)