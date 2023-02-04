{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ExistentialQuantification #-}

module TypeInfo
( TypeInfo(..)
, ClassAccessFlags(..)
, FieldDeclaration(..)
, FieldAttributes(..)
, MethodSignature(..)
, MethodAttributes(..)
, MethodDeclaration(..)
, Type(..)
, getClassTypeInfo
, isSubtypeOf
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
, getErasedMethodSignature
, getTypeMethodDeclarationName
, getErasedTypeName
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

class TypeInfo_ t where
  getTypeName :: t -> ValidTypeName
  getTypeParent :: t -> ValidTypeClassType
  getTypeImplements :: t -> [ValidTypeClassType]
  getTypeFields :: t -> [FieldDeclaration]
  getTypeMethods :: t -> [MethodDeclaration]
  getTypeAccessFlags :: t -> ClassAccessFlags
  getTypeParameters :: t -> [CP.ClassPathTypeParameter]
  getTypeFieldDeclaration :: t -> P.SimpleName -> Maybe FieldDeclaration
  getTypeFieldDeclaration ti nm =
    List.find (\(FieldDeclaration f) -> nm == getFieldName f) (getTypeFields ti)
  getErasedType :: t -> ValidTypeName

  {-- Get a list of method declartions that are potentially applicable to the provided MethodSignature -}
  getTypePotentiallyApplicableMethods :: t -> MethodSignature -> StateT ValidTypeClassData IO [MethodDeclaration]
  getTypePotentiallyApplicableMethods ti signature@(MethodSignature searchName searchParams) = do
    let candidateMatchingMethods = List.filter (\(MethodDeclaration m) ->
          P.deconstructSimpleName (getMethodName m) == searchName) (getTypeMethods ti)
    let returnList = List.filter (\(MethodDeclaration m) ->
          length (getMethodParams m) == length searchParams) candidateMatchingMethods
    return $ trace ("potentiallyApplicableMethod::"++show (fmap (\(MethodDeclaration m) -> show m) returnList)) returnList

instance TypeInfo_ ValidTypeClazz where
  getTypeName ValidTypeClazz {..} = vcName
  getTypeParent ValidTypeClazz {..} = fst vcParent
  getTypeImplements _ = []
  getTypeFields ValidTypeClazz {..} = fmap FieldDeclaration vcFields
  getTypeMethods ValidTypeClazz {..} = fmap MethodDeclaration vcMethods
  getTypeAccessFlags ValidTypeClazz {..} = ClassAccessFlags { caAbstract = P.CAbstract `elem` vcAccessFlags
                                                            , caInterface = P.CInterface `elem` vcAccessFlags}
  getTypeParameters _ = []
  getErasedType ValidTypeClazz{..} = vcName

instance TypeInfo_ ClassDescriptor where
  getTypeName ClassDescriptor {..} = ClassPathVTN name
  getTypeParent ClassDescriptor {..} = ClassPathCT parent
  getTypeImplements ClassDescriptor {..} = fmap ClassPathCT (S.toList interfaceClasses)
  getTypeFields ClassDescriptor {..} = fmap FieldDeclaration fields
  getTypeMethods ClassDescriptor {..} = fmap MethodDeclaration (filter concreteMethod methods)
  getTypeAccessFlags ClassDescriptor {..} = ClassAccessFlags { caAbstract = FS.match accessFlags CP.cAbstractMaskedValue
                                                             , caInterface = FS.match accessFlags CP.cInterfaceMaskedValue
                                                             }
  getTypeParameters ClassDescriptor {..} = V.toList typeParameters
  getErasedType ClassDescriptor {..} = ClassPathVTN name

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
  getErasedMethodSignature :: m -> MethodSignature

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
  getErasedMethodSignature vtm = getMethodSignature vtm

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
  getErasedMethodSignature method = MethodSignature (mname method) (getErasedMethodParams method)

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

getTypeMethodDeclarationName :: MethodDeclaration -> P.SimpleName
getTypeMethodDeclarationName (MethodDeclaration m) = getMethodName m

data Type = I
          | Z
          | U -- Unsupported primitive
          | L !ValidTypeClassType

instance Show Type where
  show I = "I"
  show Z = "Z"
  show U = "Unsupported"
  show (L t) = Prelude.show t

instance Eq Type where
  (==) t1 t2 = Prelude.show t1 == Prelude.show t2

instance Show MethodSignature where
  show (MethodSignature nm paramTypes) = T.unpack nm++"("++List.foldl' (\str p -> str++Prelude.show p) "" paramTypes++")"

convertClassPathType :: ClassPathType -> Type
convertClassPathType jts | isClassPathTypeBoolean jts = Z
convertClassPathType cpt | isClassPathTypeInteger cpt = I
convertClassPathType cpt | isClassPathTypeReference cpt = case getClassPathTypeReference cpt of
                                                            Just cpcrt -> L (ClassPathCT cpcrt)
                                                            Nothing -> undefined
convertClassPathType cpt = trace ("Unsupported ClassPathType: "++show cpt) U

isTypeSupported :: Type -> Bool
isTypeSupported I = True
isTypeSupported Z = True
isTypeSupported U = False
isTypeSupported (L _) = True

getClassTypeInfo :: ValidTypeClassType -> StateT ValidTypeClassData IO TypeInfo
getClassTypeInfo (ClassPathCT (CPClassReferenceType cpvtn _)) = do
  (classPath, classMap) <- get
  cd <- lift $ evalStateT (getClassPathValidType cpvtn) classPath
  return $ TypeInfo cd
getClassTypeInfo (LocalCT (LocalClassType vtn _)) = do
  (classPath, classMap) <- get
  return $ TypeInfo (classMap Map.! vtn)

isSubtypeOf :: TypeInfo -> TypeInfo -> StateT ValidTypeClassData IO Bool
isSubtypeOf (TypeInfo childTI) (TypeInfo parentTI) = do
  childImplements <- mapM getClassTypeInfo (getTypeImplements childTI)
  isSubtype <- (getTypeName childTI == getTypeName parentTI ||) <$>
    foldM (\r ti -> if r then return r else isSubtypeOf ti (TypeInfo parentTI)) False childImplements
  if isSubtype
    then return True
    else do
      let childParentQName = getTypeParent childTI
          childParentErasedType = getErasedType childTI
      if childParentErasedType == getTypeName childTI -- Only java/lang/Object has itself as a parent
        then return False
        else do
          childParentTI <- getClassTypeInfo childParentQName
          isSubtypeOf childParentTI (TypeInfo parentTI)

{--getFieldDeclaration (Path ClassDescriptor {..}) nm =
  let maybeMatchingField = List.find (\CP.Field {..} -> showt nm == fname) fields
  in
    fmap (\CP.Field {..} ->
      let faStatic = FS.match faccessFlags CP.fStaticMaskedValue
      in
        FieldDeclaration (FieldAttributes {..}) (convertClassPathType ftype) fname)
    maybeMatchingField
-}

getErasedTypeName :: ValidTypeClassType -> ValidTypeName
getErasedTypeName (LocalCT (LocalClassType vtn _ )) = vtn
getErasedTypeName (ClassPathCT cpcrt) = 
  let (CPClassReferenceType vtn _) = eraseParameterizedType cpcrt
  in ClassPathVTN vtn