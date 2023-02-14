{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}

module TypeInfo
( TypeInfo(..)
, ClassAccessFlags(..)
, FieldDeclaration(..)
, FieldAttributes(..)
, MethodSignature(..)
, MethodAttributes(..)
, MethodDeclaration(..)
, Type(..)
, ParamaterizedTypeEnvironmentMap
, getClassTypeInfo
, getClassTypeInfo'
, getTypeName
, getTypeParent
, getTypeFields
, getTypeMethods
, getTypeAccessFlags
, getTypeFieldDeclaration
, getTypePotentiallyApplicableMethods
, isTypeSupported
, getFieldName
, getFieldType
, getFieldAttributes
, getMethodName
, getMethodType
, getMethodParams
, getErasedMethodParams
, getMethodAttributes
, getMethodSignature
, getErasedTypeName
, getErasedMethodSignature
, buildParameterizedTypeEnvironmentMap
, getSignatureWithResolvedTypeParams
, getTypeImplements
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
import Control.Monad.Trans.State.Strict (StateT,get,put,runStateT,evalStateT)
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
  getTypeParameters :: t -> [TypeParameterDeclaration]
  getTypeFieldDeclaration :: t -> P.SimpleName -> Maybe FieldDeclaration
  getTypeFieldDeclaration ti nm =
    List.find (\(FieldDeclaration f) -> nm == getFieldName f) (getTypeFields ti)
  getTypeErasedType :: t -> TypeCheckerValidTypeQualifiedNameWrapper

  {-- Get a list of method declartions that are potentially applicable to the provided MethodSignature -}
  getTypePotentiallyApplicableMethods :: t -> MethodSignature -> StateT ValidTypeClassData IO [MethodDeclaration]
  getTypePotentiallyApplicableMethods ti signature@(MethodSignature searchName searchParams) = do
    let candidateMatchingMethods = List.filter (\(MethodDeclaration m) ->
          P.deconstructSimpleName (getMethodName m) == searchName) (getTypeMethods ti)
    let returnList = List.filter (\(MethodDeclaration m) ->
          length (getMethodParams m) == length searchParams) candidateMatchingMethods
    return $ trace ("potentiallyApplicableMethod::"++ show (getValidTypeQName (getTypeName ti)) ++ show (fmap (\(MethodDeclaration m) -> show m) returnList)) returnList


instance TypeInfo_ ValidTypeClazz where
  getTypeName ValidTypeClazz {..} = vcName
  getTypeParent ValidTypeClazz {..} = fst vcParent
  getTypeImplements _ = []
  getTypeFields ValidTypeClazz {..} = fmap FieldDeclaration vcFields
  getTypeMethods ValidTypeClazz {..} = fmap MethodDeclaration vcMethods
  getTypeAccessFlags ValidTypeClazz {..} = ClassAccessFlags { caAbstract = P.CAbstract `elem` vcAccessFlags
                                                            , caInterface = P.CInterface `elem` vcAccessFlags}
  getTypeParameters _ = []
  getTypeErasedType ValidTypeClazz{..} = vcName

instance TypeInfo_ ClassDescriptor where
  getTypeName ClassDescriptor {..} = name
  getTypeParent ClassDescriptor {..} = parent
  getTypeImplements ClassDescriptor {..} = S.toList interfaceClasses
  getTypeFields ClassDescriptor {..} = fmap FieldDeclaration fields
  getTypeMethods ClassDescriptor {..} = fmap MethodDeclaration (filter concreteMethod methods)
  getTypeAccessFlags ClassDescriptor {..} = ClassAccessFlags { caAbstract = FS.match accessFlags CP.cAbstractMaskedValue
                                                             , caInterface = FS.match accessFlags CP.cInterfaceMaskedValue
                                                             }
  getTypeParameters ClassDescriptor {..} = fmap TypeParameterDeclaration (V.toList typeParameters)
  getTypeErasedType ClassDescriptor {..} = name

concreteMethod :: CP.Method -> Bool
concreteMethod CP.Method {..} = not (FS.match maccessFlags CP.mSyncheticMaskedValue) && not (FS.match maccessFlags CP.mBridgeMaskedValue)

class Field_ f where
  getFieldName :: f -> P.SimpleName
  getFieldType :: f -> Type
  getFieldAttributes :: f -> FieldAttributes

instance Field_ ValidTypeField where
  getFieldName ValidTypeField {..} = fst vfName
  getFieldType ValidTypeField {..} = L vfType
  getFieldAttributes ValidTypeField {..} = FieldAttributes { faStatic=False }

instance Field_ Field where
  getFieldName CP.Field {..} = P.constructSimpleName fname
  getFieldType CP.Field {..} = convertClassPathType ftype
  getFieldAttributes CP.Field {..} = FieldAttributes { faStatic=FS.match faccessFlags CP.fStaticMaskedValue }

class Method_ m where
  getMethodName :: m -> P.SimpleName
  getMethodType :: m -> Type
  getMethodParams :: m -> [Type]
  getErasedMethodParams :: m -> [Type]
  getMethodAttributes :: m -> MethodAttributes
  getMethodSignature :: m -> MethodSignature

instance Method_ ValidTypeMethod where
  getMethodName ValidTypeMethod {..} = fst vmName
  getMethodType ValidTypeMethod {..} = L vmType
  getMethodParams ValidTypeMethod {..} = fmap (L . vpType) (V.toList vmParams)
  getErasedMethodParams vtm = getMethodParams vtm
  getMethodAttributes ValidTypeMethod {..} = MethodAttributes { maStatic=False
                                                              , maAbstract=case vmMaybeImpl of Just _ -> False; Nothing -> True
                                                              }
  getMethodSignature method@ValidTypeMethod {..} =
    let (SimpleName mname, _) = vmName
    in
      MethodSignature mname (getMethodParams method)

instance Method_ Method where
  getMethodName CP.Method {..} = P.constructSimpleName mname
  getMethodType m = convertClassPathType (mapMethodToResultType m)
  getMethodParams m = fmap convertClassPathType (CP.mapMethodToParamTypeList m)
  getErasedMethodParams method@CP.Method{..} =
    fmap (convertClassPathType . eraseRefType (V.toList mclassTypeParameters)) (mapMethodToParamTypeList method)
  getMethodAttributes CP.Method {..} =  MethodAttributes { maStatic=FS.match maccessFlags CP.mStaticMaskedValue
                                                         , maAbstract=FS.match maccessFlags CP.mAbstractMaskedValue
                                                         }
  getMethodSignature method = MethodSignature (mname method) (getMethodParams method)

class TypeParameter_ p where
  getTypeParameterName :: p -> SimpleName
  getTypeParameterBounds :: p -> TypeParameterBoundDeclaration

class TypeParameterBound_ b where
  getTypeParameterBoundTypeBoundTypeVariable :: b -> Maybe SimpleName
  getTypeParameterBoundTypeBoundClass :: b -> Maybe TypeCheckerClassReferenceTypeWrapper
  getTypeParameterBoundTypeBoundAdditionalBounds :: b -> Maybe [TypeCheckerClassReferenceTypeWrapper]

instance TypeParameter_ CP.ClassPathTypeParameter where
  getTypeParameterName (CP.CPTypeParameter nm _) = nm
  getTypeParameterBounds (CP.CPTypeParameter _ (Just bounds)) = TypeParameterBoundDeclaration bounds
  getTypeParameterBounds (CP.CPTypeParameter _ Nothing) = TypeParameterBoundDeclaration objectTypeParameterBound

instance TypeParameterBound_ CP.ClassPathTypeBound where
  getTypeParameterBoundTypeBoundTypeVariable cptb =
    case cptb of
      (CP.CPTypeVariableTypeBound sn) -> Just sn
      (CP.CPClassTypeTypeBound _ _) -> Nothing
  getTypeParameterBoundTypeBoundClass cptb =
    case cptb of
      (CP.CPClassTypeTypeBound cpcrt _) -> Just cpcrt
      (CP.CPTypeVariableTypeBound _) -> Nothing
  getTypeParameterBoundTypeBoundAdditionalBounds cptb =
    case cptb of
      (CP.CPClassTypeTypeBound _ additional) -> Just (S.toList additional)
      (CP.CPTypeVariableTypeBound _) -> Nothing

data ClassAccessFlags = ClassAccessFlags { caAbstract :: Bool
                                         , caInterface :: Bool
                                         } deriving Show

newtype FieldAttributes = FieldAttributes {faStatic :: Bool} deriving Show

data FieldDeclaration = forall f.(Field_ f) => FieldDeclaration f

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

data TypeParameterDeclaration = forall p. (Show p, TypeParameter_ p) => TypeParameterDeclaration p

data TypeParameterBoundDeclaration = forall b. (Show b, TypeParameterBound_ b) => TypeParameterBoundDeclaration b

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
  show (MethodSignature nm paramTypes) = T.unpack nm++"("++List.foldl' (\str p -> str++Prelude.show p) "" paramTypes++")"

type ParamaterizedTypeEnvironmentMap = Map.Map SimpleName TypeCheckerTypeArgument

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

getClassTypeInfo :: TypeCheckerClassReferenceTypeWrapper -> StateT ValidTypeClassData IO TypeInfo
getClassTypeInfo (TypeCheckerClassReferenceTypeWrapper vtqnw _) = getClassTypeInfo' vtqnw

getClassTypeInfo' :: TypeCheckerValidTypeQualifiedNameWrapper -> StateT ValidTypeClassData IO TypeInfo
getClassTypeInfo' vtqnw = do
  typeInfoData <- getClassTypeInfoData vtqnw
  return $ case typeInfoData of
    LocalTypeInfoData vtc -> TypeInfo vtc
    ClassPathTypeInfoData cd -> TypeInfo cd


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

getErasedTypeName :: TypeCheckerClassReferenceTypeWrapper -> TypeCheckerValidTypeQualifiedNameWrapper
getErasedTypeName (TypeCheckerClassReferenceTypeWrapper vtqn _) = vtqn

getErasedMethodSignature :: MethodDeclaration -> MethodSignature
getErasedMethodSignature (MethodDeclaration method) = MethodSignature (showt (getMethodName method)) (getErasedMethodParams method)

getErasedType :: Type -> Type
getErasedType I = I
getErasedType Z = Z
getErasedType U = U
getErasedType (L (TypeCheckerClassReferenceTypeWrapper qn _)) = L (TypeCheckerClassReferenceTypeWrapper qn Nothing)
getErasedType id@(T sn) = id

buildParameterizedTypeEnvironmentMap :: TypeInfo -> [TypeCheckerTypeArgument] -> ParamaterizedTypeEnvironmentMap
buildParameterizedTypeEnvironmentMap (TypeInfo ti) typeArgs =
  let genericTypeParams = getTypeParameters ti
  in
    Map.fromList (
    zip (
      fmap
        (\(TypeParameterDeclaration tp) -> getTypeParameterName tp)
        genericTypeParams)
    typeArgs)

getSignatureWithResolvedTypeParams :: ParamaterizedTypeEnvironmentMap -> MethodDeclaration -> [Type]
getSignatureWithResolvedTypeParams envMap (MethodDeclaration md) =
  let params = fmap
                (\t -> case t of
                        I -> I
                        Z -> Z
                        U -> U
                        L crtw -> L crtw
                        T sn -> case envMap Map.!? sn of
                          Nothing -> error ("Undefined type variable: ") -- ++ show sn ++ " in " ++ show envMap)
                          Just (TypeCheckerTypeArgument _ rtw) -> case getTypeCheckerReferenceTypeClass rtw of
                            Nothing -> undefined -- only class references are supported for now
                            Just crtw -> L crtw)
                (getMethodParams md)
  in
    params
