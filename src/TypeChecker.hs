{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StrictData #-}

module TypeChecker
  ( typeCheck
  , TypeError
  , TypedAbstraction(..)
  , TypedStaticAbstraction(..)
  , TypedValue(..)
  , TypedTerm(..)
  , TypedReferenceTerm(..)
  , TypedConstructorInvocation(..)
  , TypedAssignment(..)
  , TypedMethod(..)
  , TypedMethodImplementation(..)
  , TypedClazz(..)
  , getTypedTermType
  , P.deconstructQualifiedName
  , ReferenceType
  , TypedTypeName(..)
  , getOrderedParentTypes
  , isSubtypeOf
  , substituteTypeArgument
  ) where

import Control.Monad.Trans.State.Strict (StateT,get,put,evalStateT,runStateT)
import Control.Monad.Trans.Reader (ReaderT, Reader, runReader, runReaderT, ask)
import Control.Monad (join,foldM,liftM,liftM2, zipWithM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except ( ExceptT, runExceptT, throwE )
import Control.Monad.Extra ( foldM, ifM, join, filterM, anyM )
import Control.Monad.ListM (unionByM, sortByM)
import Control.Monad.Loops (unfoldrM)
import qualified Control.Applicative as AP
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Either as Either
import qualified Data.Maybe as Maybe
import qualified Data.Text as T
import qualified Data.Validation as V
import qualified Data.FlagSet as FS
import qualified Data.Vector as VT
import qualified Data.Foldable as F

import TextShow
import Data.Word ( Word8 )
import qualified Parser as P
import Text.Parsec.Pos ( SourcePos )
import qualified ClassPath as CP
import Debug.Trace
import Data.Maybe (mapMaybe)
import Data.Int (Int32)
import Parser2
import TypeCheckerTypes
import Data.ByteString.Builder.Prim (condB)
import qualified Data.Sequence.Internal.Sorting as P
import TypeValidator
import TypeInfo
import Environment
import GHC.Stack (errorWithStackTrace)
import Data.Foldable (foldrM)
import qualified Control.Monad as List

data TypedAbstraction = TypedFieldAccess { fName :: P.SimpleName
                                         , fTyp :: Type
                                         , fErasedType :: Type
                                         }
                      | TypedMethodInvocation { mName :: P.SimpleName
                                              , mTyp :: Type
                                              , mArgumentTyps :: [Type]
                                              , mArgumentTerms :: [TypedTerm]
                                              , mErasedType :: Type
                                              , mErasedArgumentTypes :: [Type]
                                              }
                      | TypedInterfaceMethodInvocation  { iName :: P.SimpleName
                                                        , iTyp :: Type
                                                        , iArgumentTyps :: [Type]
                                                        , iArgumentTerms :: [TypedTerm]
                                                        , iErasedType :: Type
                                                        , iErasedArgumentTypes :: [Type]
                                                        }
                      | TypedSuperMethodInvocation  { smName :: P.SimpleName
                                                    , smTyp :: Type
                                                    , smParamTyps :: [Type]
                                                    , smTerms :: [TypedTerm]
                                                    }
                      deriving Show

data TypedStaticAbstraction = TypedStaticFieldAccess { tfName :: P.SimpleName
                                                     , tfTyp :: Type
                                                     , tfErasedType :: Type
                                                     }
                      | TypedStaticMethodInvocation { tmName :: P.SimpleName
                                                    , tmTyp :: Type
                                                    , tmArgumentTyps :: [Type]
                                                    , tmArguments :: [TypedTerm]
                                                    , tmErasedType :: Type
                                                    , tmErasedArgumentTypes :: [Type]
                                                    }
                      | TypedStaticInterfaceMethodInvocation { tiName :: P.SimpleName
                                                             , tiTyp :: Type
                                                             , tiArgumentTyps :: [Type]
                                                             , tiArguments :: [TypedTerm]
                                                             , tiErasedType :: Type
                                                             , tiErasedArgumentTypes :: [Type]
                                                             }
                      deriving Show

data TypedValue = TypedVariable {vPosition :: Word8, vTyp :: Type}
                | TypedIntegerLiteral {iValue :: Int32 }
                | TypedStringLiteral {sValue :: String }
                | TypedBooleanLiteral {bValue :: Bool }
                | TypedObjectCreation { ocTyp :: TypeCheckerClassReferenceTypeWrapper
                                      , ocArgumentTypes :: [Type]
                                      , ocArgumentTerms :: [TypedTerm]
                                      , ocErasedArgumentType :: [Type]
                                      }
                deriving Show

data TypedTerm = TypedValue TypedValue
               | TypedApplication TypedReferenceTerm TypedAbstraction
               | TypedStaticApplication TypedTypeName TypedStaticAbstraction
               | TypedCast TypedReferenceTerm
               | TypedConditional TypedTerm TypedTerm TypedTerm Type
               deriving Show

newtype TypedTypeName = TypedTypeName TypeCheckerValidTypeQualifiedNameWrapper deriving Show

data TypedReferenceTerm = TypedReferenceTerm TypeCheckerReferenceTypeWrapper TypedTerm deriving Show

data TypedConstructorInvocation = NewTypedConstructorInvocation TypeCheckerValidTypeQualifiedNameWrapper [Type] [TypedTerm] deriving Show

data TypedAssignment = NewTypedAssignment TypedTerm TypedTerm deriving Show

data TypedMethod = NewTypedMethod P.SimpleName [ValidTypeParameter] TypeCheckerJavaType (Maybe TypedMethodImplementation)
                 deriving Show

data TypedClazz = NewTypedClazz [P.ClassAccessFlag] TypeCheckerValidTypeQualifiedNameWrapper TypeCheckerValidTypeQualifiedNameWrapper [ValidTypeField] [TypedMethod]
                deriving Show

data TypedMethodImplementation = TypedMethodImpl TypedTerm
                               | TypedConstructorImpl TypedConstructorInvocation [TypedAssignment]
                               deriving Show

init' = SimpleName (T.pack "<init>")

getValidTypeTermPosition :: ValidTypeTerm -> SourcePos
getValidTypeTermPosition (ValidTypeValue (ValidTypeVariable pos _)) = pos
getValidTypeTermPosition (ValidTypeValue (ValidTypeIntegerLit pos _)) = pos
getValidTypeTermPosition (ValidTypeValue (ValidTypeStringLit pos _)) = pos
getValidTypeTermPosition (ValidTypeValue (ValidTypeBooleanLit pos _)) = pos
getValidTypeTermPosition (ValidTypeValue (ValidTypeObjectCreation pos _ _ _)) = pos
getValidTypeTermPosition (ValidTypeCast (ValidTypeRefTypeDeclaration pos _) _) = pos
getValidTypeTermPosition (ValidTypeApplication (ValidTypeApplicationTargetTerm t) _) = getValidTypeTermPosition t
getValidTypeTermPosition (ValidTypeApplication (ValidTypeApplicationTargetTypeName (ValidTypeTypeName pos _)) _) = pos
getValidTypeTermPosition (ValidTypeConditional t _ _) = getValidTypeTermPosition t

getTypedTermType :: TypedTerm -> Type
getTypedTermType (TypedValue TypedVariable {vTyp=tp}) = tp
getTypedTermType (TypedValue TypedIntegerLiteral {}) = I
getTypedTermType (TypedValue TypedStringLiteral {}) = L CP.createValidTypeClassTypeString
getTypedTermType (TypedValue TypedBooleanLiteral {}) = Z
getTypedTermType (TypedValue TypedObjectCreation {ocTyp=crtw}) = L crtw
getTypedTermType (TypedApplication _ TypedFieldAccess {fTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedMethodInvocation {mTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedInterfaceMethodInvocation {iTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedSuperMethodInvocation {smTyp=tp}) = tp
getTypedTermType (TypedStaticApplication _ TypedStaticFieldAccess {tfTyp=tp}) = tp
getTypedTermType (TypedStaticApplication _ TypedStaticMethodInvocation {tmTyp=tp}) = tp
getTypedTermType (TypedStaticApplication _ TypedStaticInterfaceMethodInvocation {tiTyp=tp}) = tp
getTypedTermType (TypedCast (TypedReferenceTerm (TypeCheckerClassRefType tp) _)) = L tp
getTypedTermType (TypedCast (TypedReferenceTerm (TypeCheckerTypeVariableRefType tv) _)) = T tv
getTypedTermType (TypedCast (TypedReferenceTerm (TypeCheckerArrayRefType tv) _)) = undefined
getTypedTermType (TypedConditional _ _ _ t) = t

getTypedTermErasedType :: [TypeCheckerTypeParameter] -> TypedTerm -> Type
getTypedTermErasedType typeParams (TypedValue TypedVariable {vTyp=tp}) = getErasedType typeParams tp
getTypedTermErasedType _ (TypedValue TypedIntegerLiteral {}) = I
getTypedTermErasedType _ (TypedValue TypedStringLiteral {}) = L CP.createValidTypeClassTypeString
getTypedTermErasedType _ (TypedValue TypedBooleanLiteral {}) = Z
getTypedTermErasedType typeParams (TypedValue TypedObjectCreation {ocTyp=crtw}) = getErasedType typeParams (L crtw)
getTypedTermErasedType typeParams (TypedApplication _ TypedFieldAccess {..}) = fErasedType
getTypedTermErasedType typeParams (TypedApplication _ TypedMethodInvocation {..}) = mErasedType
getTypedTermErasedType typeParams (TypedApplication _ TypedInterfaceMethodInvocation {..}) = iErasedType
getTypedTermErasedType typeParams (TypedApplication _ TypedSuperMethodInvocation {smTyp=tp}) = getErasedType typeParams tp
getTypedTermErasedType typeParams (TypedStaticApplication _ TypedStaticFieldAccess {..}) = tfErasedType
getTypedTermErasedType typeParams (TypedStaticApplication _ TypedStaticMethodInvocation {..}) = tmErasedType
getTypedTermErasedType typeParams (TypedStaticApplication _ TypedStaticInterfaceMethodInvocation {..}) = tiErasedType
getTypedTermErasedType typeParams (TypedCast (TypedReferenceTerm (TypeCheckerClassRefType tp) _)) = getErasedType typeParams (L tp)
getTypedTermErasedType typeParams (TypedCast (TypedReferenceTerm (TypeCheckerTypeVariableRefType tv) _)) = getErasedType typeParams (T tv)
getTypedTermErasedType typeParams (TypedCast (TypedReferenceTerm (TypeCheckerArrayRefType tv) _)) = undefined
getTypedTermErasedType typeParams (TypedConditional _ _ _ t) = getErasedType typeParams t

typeCheck :: LocalClasses -> StateT CP.ClassPath IO (Either [TypeError] [TypedClazz])
typeCheck classMap = do
  classPath <- get
  (typedClazzE,(classPath',_)) <- lift $ runStateT typeCheck' (classPath,classMap)
  put classPath'
  return typedClazzE

typeCheck' :: StateT ClassData IO (Either [TypeError] [TypedClazz])
typeCheck' = do
  validTypesE <- transformToValidTypes
  case validTypesE of
    V.Failure typeErrors -> return $ Left typeErrors
    V.Success validTypes -> do
      (classPath,localClasses) <- get
      let validTypeMap =
            List.foldl' (\classMap validTypeClass@ValidTypeClazz {..} ->
              Map.insert vcName validTypeClass classMap)
            Map.empty
            validTypes
      (typeErrorsV,(classPath',_)) <- lift $ runStateT typeCheckValidTypes (classPath,validTypeMap)
      case typeErrorsV of
        V.Failure typeErrors -> return $ Left typeErrors
        V.Success _ -> do
          (typedClazzsE, (classPath'',_)) <- lift $ runStateT transformToTyped (classPath',validTypeMap)
          put (classPath'',localClasses)
          case typedClazzsE of
            Left typeErrors -> return $ Left typeErrors
            Right typedClazzs -> return $ Right typedClazzs

typeCheckValidTypes :: StateT ValidTypeClassData IO (V.Validation [TypeError] ())
typeCheckValidTypes = do
  e1 <- checkForDuplicateTypeErrors
  e2 <- checkForClassInheritenceCycles
  e3 <-checkForInvalidParameterizedTypeTypeArguments
  let grp1 = e1 *> e2 *> e3
  case grp1 of
    V.Failure errors -> return $ V.Failure errors
    V.Success _ -> do
      e4 <- checkForAbstractClassSubClassErrors
      e5 <- checkForNonReturnTypeSubstitutableOverrides
      e6 <- checkForConstructorsUnassignedFieldErrors
      return $ e4 *> e5 *> e6

transformToTyped :: StateT ValidTypeClassData IO (Either [TypeError] [TypedClazz])
transformToTyped = do
  typeData@(_,classMap) <- get
  clazzList <- foldM (\list cls -> (list ++) <$> fmap (: []) (V.toEither <$> getTypedClazz cls)) [] classMap
  let (typeErrors, typedClazzs) = Either.partitionEithers clazzList
  if not (null typeErrors)
    then return $ Left (concat typeErrors)
    else return $ Right typedClazzs

checkForDuplicateTypeErrors :: StateT ValidTypeClassData IO (V.Validation [TypeError] ())
checkForDuplicateTypeErrors = do
  typeData@(_,classMap) <- get
  let errors = foldr (\cls list -> getDuplicateFields cls ++ getDuplicateMethods cls ++ list) [] classMap
  return $ case errors of
    [] -> V.Success ()
    _ -> V.Failure errors

checkForInvalidParameterizedTypeTypeArguments :: StateT ValidTypeClassData IO (V.Validation [TypeError] ())
checkForInvalidParameterizedTypeTypeArguments = do
  (_,classMap) <- get
  foldM (\list cls -> do
      e1 <- getParentInvalidParameterizedTypeTypeArguments cls
      e2 <- getFieldInvalidParameterizedTypeTypeArguments cls
      e3 <- getMethodInvalidParameterizedTypeTypeArguments cls
      return $ list *> e1 *> e2 *> e3)
    (pure ())
    classMap

checkForClassInheritenceCycles :: StateT ValidTypeClassData IO (V.Validation [TypeError] ())
checkForClassInheritenceCycles = checkForErrors getClassInheritenceCycleErrors

checkForAbstractClassSubClassErrors :: StateT ValidTypeClassData IO (V.Validation [TypeError] ())
checkForAbstractClassSubClassErrors = checkForErrors getAbstractClassSubClassErrors

checkForNonReturnTypeSubstitutableOverrides :: StateT ValidTypeClassData IO (V.Validation [TypeError] ())
checkForNonReturnTypeSubstitutableOverrides = checkForErrors getNonReturnTypeSubstitutableOverrideErrors

checkForConstructorsUnassignedFieldErrors :: StateT ValidTypeClassData IO (V.Validation [TypeError] ())
checkForConstructorsUnassignedFieldErrors = checkForErrors getConstructorsUnassignedFieldErrors

checkForErrors :: (ValidTypeClazz -> StateT ValidTypeClassData IO [TypeError]) -> StateT ValidTypeClassData IO (V.Validation [TypeError] ())
checkForErrors getErrorsFunction = do
  typeData@(_,classMap) <- get
  errors <- foldM (\list cls -> (list ++) <$> getErrorsFunction cls) [] classMap
  return $ case errors of
    [] -> V.Success ()
    _ -> V.Failure errors

getType :: ValidTypeTerm -> ReaderT Environment (StateT ValidTypeClassData IO) (V.Validation [TypeError] TypedTerm)
getType (ValidTypeValue (ValidTypeVariable pos x)) = do
  env <- ask
  case env !? x of
    Just (tp,ndx) -> return $ V.Success $ TypedValue (TypedVariable {vPosition=fromIntegral ndx :: Word8,vTyp=tp})
    Nothing -> return $ V.Failure [TypeError ("Undefined variable: "++show x) pos]

getType (ValidTypeValue (ValidTypeIntegerLit pos v)) = do
  return $ V.Success $ TypedValue (TypedIntegerLiteral {iValue=v})

getType (ValidTypeValue (ValidTypeStringLit pos s)) = do
  return $ V.Success $ TypedValue (TypedStringLiteral {sValue=s})

getType (ValidTypeValue (ValidTypeBooleanLit pos b)) = do
  return $ V.Success $ TypedValue (TypedBooleanLiteral {bValue=b})

getType (ValidTypeValue (ValidTypeObjectCreation pos tp@(TypeCheckerClassReferenceTypeWrapper _ maybeTypeArgs) arguments constructorTypeArgs)) = do
  cond <- lift $ isConcreteClass tp
  if not cond
    then return $ V.Failure [TypeError ("Illegal creation of abstract type: "++show tp) pos]
    else do
      typeData <- lift get
      (TypeInfo ti) <- lift $ getClassTypeInfo tp
      invalidTypeArgsV <- lift $ getInvalidParameterizedTypeTypeArguments pos (TypeCheckerJavaReferenceType (TypeCheckerClassRefType tp))
      argumentTermsV <- sequenceA <$> mapM getType arguments
      typedValueV <- case V.toEither argumentTermsV of
        Left errors -> return $ V.Failure errors
        Right argumentTerms -> do
          let paramaterizedTypeEnvMap = case maybeTypeArgs of
                Nothing -> Map.empty
                Just typeArgs -> buildTypeParamEnvironment (getTypeParameters ti) typeArgs
          eitherMethodInvocationExists <- lift $ getConstructorDeclaration tp (fmap getTypedTermType argumentTerms) constructorTypeArgs
          case eitherMethodInvocationExists of
            Left errStr -> return $ V.Failure [TypeError errStr pos]
            Right methodDeclaration@(MethodDeclaration m) -> do
              argumentTypes <- lift $ getSignatureWithResolvedTypeParams (getTypeName ti) paramaterizedTypeEnvMap constructorTypeArgs methodDeclaration
              erasedArgumentTypes <- lift $ getSignatureWithErasedTypeParams (getTypeName ti) paramaterizedTypeEnvMap constructorTypeArgs methodDeclaration
              argumentTermsNarrowCastIfNecessary <- lift $
                zipWithM addNarrowingCast argumentTerms argumentTypes
              return $ V.Success $
                TypedValue 
                  (TypedObjectCreation { ocTyp=tp
                                       , ocArgumentTypes=argumentTypes
                                       , ocErasedArgumentType=erasedArgumentTypes
                                       , ocArgumentTerms=argumentTermsNarrowCastIfNecessary
                                       })
      return $ typedValueV <* invalidTypeArgsV

getType (ValidTypeCast (ValidTypeRefTypeDeclaration pos tp) t) = do
  typeData <- lift get
  typedTermV <- getType t
  case typedTermV of
    V.Failure tes -> return $ V.Failure tes
    V.Success typedTerm -> do
      let typedTermType = getTypedTermType typedTerm
      let termTypeInfo = getBoxedType (getTypedTermType typedTerm)
      let castTypeInfo = tp
      isSubtype <- lift $ isSubtypeOf castTypeInfo (TypeCheckerClassRefType termTypeInfo)
      if isSubtype
        then return $ V.Success (TypedCast (TypedReferenceTerm tp typedTerm))
        else return $ V.Failure [TypeError ("Invalid cast: "++show tp) pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTerm t) (ValidTypeFieldAccess pos nm)) = do
  typedTermV <- getType t
  case typedTermV of
    V.Failure tes -> return $ V.Failure tes
    V.Success typedTerm -> case getTypedTermType typedTerm of
      L crtw@(TypeCheckerClassReferenceTypeWrapper typeName maybeTypeArgs) -> do
        termType@(TypeInfo termTi) <- lift $ getClassTypeInfo' typeName
        maybeFieldDeclaration <- lift $ getFieldDeclaration termType nm
        case maybeFieldDeclaration of
          Nothing -> return $ V.Failure [TypeError ("Undefined field: "++show nm) pos]
          Just fieldDeclaration@(FieldDeclaration f) -> do
            let typeParamEnvironment = case maybeTypeArgs of
                  Nothing -> Map.empty
                  Just typeArgs -> buildTypeParamEnvironment (getTypeParameters termTi) typeArgs
            if faStatic (getFieldAttributes f)
              then do
                tp <- lift $ getFieldTypeWithResolvedTypeParams typeName Map.empty fieldDeclaration
                erasedTp <- lift $ getFieldTypeWithErasedTypeParams typeName Map.empty fieldDeclaration
                return $
                  V.Success
                    (TypedStaticApplication
                      (TypedTypeName
                        (getErasedTypeName crtw))
                      (TypedStaticFieldAccess {tfName=nm,tfTyp=tp,tfErasedType=erasedTp}))
              else do
                tp <- lift $ getFieldTypeWithResolvedTypeParams typeName typeParamEnvironment fieldDeclaration
                erasedTp <- lift $ getFieldTypeWithErasedTypeParams typeName typeParamEnvironment fieldDeclaration
                return $
                  V.Success
                    (TypedApplication
                      (TypedReferenceTerm (TypeCheckerClassRefType crtw) typedTerm)
                      (TypedFieldAccess {fName=nm,fTyp=tp,fErasedType=erasedTp}))
      T sn -> undefined
      _ -> return $ V.Failure [TypeError "term with primitive type cannot be dereferenced" pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTerm t) (ValidTypeMethodInvocation pos nm arguments methodTypeArgs)) = do
  typedTermV <- getType t
  argumentTermsV <- sequenceA <$> mapM getType arguments
  let termTupleV = (,) <$> typedTermV <*> argumentTermsV
  case termTupleV of
    V.Failure tes -> return $ V.Failure tes
    V.Success (typedTerm,argumentTerms) -> do
      let signature = MethodSignature nm (fmap getTypedTermType argumentTerms)
      case getTypedTermType typedTerm of
        L crtw@(TypeCheckerClassReferenceTypeWrapper _ maybeTypeArguments) -> do
          eitherMethodType <- lift $ getMethodDeclaration crtw signature methodTypeArgs
          case eitherMethodType of
            Left errStr -> return $ V.Failure [TypeError errStr pos]
            Right methodDeclaration@(MethodDeclaration m) -> do
              if maStatic (getMethodAttributes m) -- static method
                then do
                  (TypeInfo ti) <- lift $ getClassTypeInfo crtw
                  returnType <- lift $ getMethodTypeWithResolvedTypeParams (getTypeName ti) Map.empty methodTypeArgs methodDeclaration
                  argumentTypes <- lift $ getSignatureWithResolvedTypeParams (getTypeName ti) Map.empty methodTypeArgs methodDeclaration
                  erasedReturnType <- lift $ getMethodTypeWithErasedTypeParams (getTypeName ti) Map.empty methodTypeArgs methodDeclaration
                  erasedArgumentTypes <- lift $ getSignatureWithErasedTypeParams (getTypeName ti) Map.empty methodTypeArgs methodDeclaration
                  argumentTermNarrowCastIfNecessary <- lift $
                    zipWithM addNarrowingCast argumentTerms argumentTypes
                  let methodInvocation =
                        if caInterface (getTypeAccessFlags ti)
                          then
                            TypedStaticInterfaceMethodInvocation
                              { tiName=nm
                              , tiTyp=returnType
                              , tiArgumentTyps=argumentTypes
                              , tiArguments=argumentTermNarrowCastIfNecessary
                              , tiErasedType=erasedReturnType
                              , tiErasedArgumentTypes=erasedArgumentTypes}
                          else
                            TypedStaticMethodInvocation
                              { tmName=nm
                              , tmTyp=returnType
                              , tmArgumentTyps=argumentTypes
                              , tmArguments=argumentTermNarrowCastIfNecessary
                              , tmErasedType=erasedReturnType
                              , tmErasedArgumentTypes=erasedArgumentTypes}
                  return $ V.Success
                        (TypedStaticApplication
                          (TypedTypeName (getErasedTypeName crtw))
                          methodInvocation)
                else do -- instance method
                  (TypeInfo ti) <- lift $ getClassTypeInfo crtw
                  let paramaterizedTypeEnvMap = case maybeTypeArguments of
                        Nothing -> Map.empty
                        Just typeArgs -> buildTypeParamEnvironment (getTypeParameters ti) typeArgs
                  returnType <- lift $ getMethodTypeWithResolvedTypeParams (getTypeName ti) paramaterizedTypeEnvMap methodTypeArgs methodDeclaration
                  argumentTypes <- lift $ getSignatureWithResolvedTypeParams (getTypeName ti) paramaterizedTypeEnvMap methodTypeArgs methodDeclaration
                  erasedReturnType <- lift $ getMethodTypeWithErasedTypeParams (getTypeName ti) paramaterizedTypeEnvMap methodTypeArgs methodDeclaration
                  erasedArgumentTypes <- lift $ getSignatureWithErasedTypeParams (getTypeName ti) paramaterizedTypeEnvMap methodTypeArgs methodDeclaration
                  argumentTermsNarrowCastIfNecessary <- lift $
                    zipWithM addNarrowingCast argumentTerms argumentTypes
                  let methodInvocation =
                        if caInterface (getTypeAccessFlags ti)
                          then
                            (TypedInterfaceMethodInvocation  {
                               iName=nm
                              ,iTyp=returnType
                              ,iArgumentTyps=argumentTypes
                              ,iArgumentTerms=argumentTermsNarrowCastIfNecessary
                              ,iErasedType=erasedReturnType
                              ,iErasedArgumentTypes=erasedArgumentTypes})
                          else
                            (TypedMethodInvocation  { mName=nm
                              ,mTyp=returnType
                              ,mArgumentTyps=argumentTypes
                              ,mArgumentTerms=argumentTermsNarrowCastIfNecessary
                              ,mErasedType=erasedReturnType
                              ,mErasedArgumentTypes=erasedArgumentTypes})
                  return $ V.Success
                    (TypedApplication
                      (TypedReferenceTerm (TypeCheckerClassRefType crtw) typedTerm)
                      methodInvocation)
        _ -> return $ V.Failure [TypeError "term with primitive type cannot be dereferenced" pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTerm t) (ValidTypeSuperMethodInvocation pos nm params)) = do
  typedTermV <- getType t
  paramTermsV <- sequenceA <$> mapM getType params
  let termTupleV = (,) <$> typedTermV <*> paramTermsV
  case termTupleV of
    V.Failure tes -> return $ V.Failure tes
    V.Success (typedTerm, paramTerms) -> do
      let signature = MethodSignature nm (fmap getTypedTermType paramTerms)
      case getTypedTermType typedTerm of
        L termTypeName -> do
          (TypeInfo termType) <- lift $ getClassTypeInfo termTypeName
          let parent = getTypeParent termType
          eitherMethodType <- lift $ getMethodDeclaration parent signature []
          case eitherMethodType of
            Left errStr -> return $ V.Failure [TypeError errStr pos]
            Right (MethodDeclaration m) -> if maStatic (getMethodAttributes m)
              then return $ V.Failure [TypeError ("Super method is abstract: "++show parent++":"++show signature) pos]
              else return $ V.Success
                (TypedApplication
                  (TypedReferenceTerm (TypeCheckerClassRefType parent) typedTerm)
                  (TypedSuperMethodInvocation {smName=nm,smTyp=getMethodType m,smParamTyps=getMethodParams m,smTerms=paramTerms}))
        _ -> return $ V.Failure [TypeError "term with primitive type cannot be dereferenced" pos]

getType (ValidTypeApplication
          (ValidTypeApplicationTargetTypeName
            tn@(ValidTypeTypeName tnPos vtqnw))
        (ValidTypeFieldAccess pos nm)) = do
    typeNameTypeInfo <- lift $ getClassTypeInfo' vtqnw
    maybeFieldDeclaration <- lift $ getFieldDeclaration typeNameTypeInfo nm
    case maybeFieldDeclaration of
      Nothing -> return $ V.Failure [TypeError ("Undefined static field: "++show vtqnw++":"++show nm) pos]
      Just (FieldDeclaration f) ->
        if faStatic (getFieldAttributes f)
          then return $
            V.Success (TypedStaticApplication
              (TypedTypeName vtqnw)
                (TypedStaticFieldAccess {tfName=nm,tfTyp=getFieldType f,tfErasedType=getErasedType [] (getFieldType f)}))
          else return $
            V.Failure [TypeError ("non-static field "++show (getFieldName f)++" cannot be referenced from a static context") pos]

getType (ValidTypeApplication
          (ValidTypeApplicationTargetTypeName
            tn@(ValidTypeTypeName tnPos vtqnw))
          (ValidTypeMethodInvocation pos nm params methodTypeArgs)) = do
  argumentTypedTermsV <- sequenceA <$> mapM getType params
  case argumentTypedTermsV of
    V.Failure tes -> return $ V.Failure tes
    V.Success argumentTypedTerms -> do
      let signature = MethodSignature nm (fmap getTypedTermType argumentTypedTerms)
      typeNameTypeInfo <- lift $ getClassTypeInfo' vtqnw
      eitherMethodInvocation <- lift $ getStaticMethodDeclaration vtqnw signature methodTypeArgs
      case eitherMethodInvocation of
        Left errStr -> return $ V.Failure [TypeError errStr pos]
        Right methodDeclaration@(MethodDeclaration m) ->
          if maStatic (getMethodAttributes m)
            then do
              (TypeInfo ti) <- lift $ getClassTypeInfo' vtqnw
              returnType <- lift $ getMethodTypeWithResolvedTypeParams (getTypeName ti) Map.empty methodTypeArgs methodDeclaration
              argumentTypes <- lift $ getSignatureWithResolvedTypeParams (getTypeName ti) Map.empty methodTypeArgs methodDeclaration
              erasedReturnType <- lift $ getMethodTypeWithErasedTypeParams (getTypeName ti) Map.empty methodTypeArgs methodDeclaration
              erasedArgumentTypes <- lift $ getSignatureWithErasedTypeParams (getTypeName ti) Map.empty methodTypeArgs methodDeclaration
              let methodInvocation =
                    if caInterface (getTypeAccessFlags ti)
                      then
                        TypedStaticInterfaceMethodInvocation
                          { tiName=nm
                          , tiTyp=returnType
                          , tiArgumentTyps=argumentTypes
                          , tiArguments=argumentTypedTerms
                          , tiErasedType=erasedReturnType
                          , tiErasedArgumentTypes=erasedArgumentTypes}
                      else
                        TypedStaticMethodInvocation
                          { tmName=nm
                          , tmTyp=returnType
                          , tmArgumentTyps=argumentTypes
                          , tmArguments=argumentTypedTerms
                          , tmErasedType=erasedReturnType
                          , tmErasedArgumentTypes=erasedArgumentTypes}
              let application = V.Success
                    (TypedStaticApplication
                      (TypedTypeName vtqnw)
                      methodInvocation)
              return application
          else
            return $ V.Failure [TypeError ("non-static method "++show (getMethodSignature m)++" cannot be referenced from a static context") pos]

getType (ValidTypeApplication
          (ValidTypeApplicationTargetTypeName
            tn@(ValidTypeTypeName tnPos vtqnw))
          (ValidTypeSuperMethodInvocation pos nm params)) = undefined

getType (ValidTypeConditional b1 t1 t2) = do
  booleanExprV <- getType b1
  term1V <- getType t1
  term2V <- getType t2
  let termTriple = (,,) <$> booleanExprV <*> term1V <*> term2V
  case termTriple of
    V.Failure tes -> return $ V.Failure tes
    V.Success (booleanExpr,term1,term2) -> do
      if not (isTypeBoolean (getUnboxedType (getTypedTermType booleanExpr)))
        then return $ V.Failure [TypeError "First term in conditional is not boolean" (getValidTypeTermPosition b1)]
        else do
          case (getTypedTermType term1, getTypedTermType term2) of
            (tp@(L qn1),L qn2) | getErasedTypeName qn1 == getErasedTypeName qn2 -> return $ V.Success (TypedConditional booleanExpr term1 term2 tp)
            (t1, t2) | isTypeBoolean (getUnboxedType t1)
                    && isTypeBoolean (getUnboxedType t2) ->
                      return $ V.Success (TypedConditional booleanExpr term1 term2 Z)
            (t1, t2) | isTypeInteger (getUnboxedType t1)
                    && isTypeInteger (getUnboxedType t2) ->
                      return $ V.Success (TypedConditional booleanExpr term1 term2 I)
            (t1, t2) -> do
              lub <- lift $ leastUpperBound [getBoxedType t1, getBoxedType t2]
              return $ V.Success (TypedConditional booleanExpr term1 term2 lub)

getDuplicateFields :: ValidTypeClazz -> [TypeError]
getDuplicateFields ValidTypeClazz {..} =
  snd $ foldr (\field@ValidTypeField {..} (fieldMap, duplicateList) ->
    let (nm,nmpos) = vfName in
    (case Map.lookup nm fieldMap of
      Nothing -> (Map.insert nm nm fieldMap, duplicateList)
      Just _ -> (fieldMap, TypeError ("Duplicate field: "++show nm) nmpos:duplicateList)))
    (Map.empty, [])
    vcFields

getParentInvalidParameterizedTypeTypeArguments :: ValidTypeClazz -> StateT ValidTypeClassData IO (V.Validation [TypeError] ())
getParentInvalidParameterizedTypeTypeArguments ValidTypeClazz{..} = do
  getInvalidParameterizedTypeTypeArguments (snd vcParent) (TypeCheckerJavaReferenceType (TypeCheckerClassRefType (fst vcParent)))

getFieldInvalidParameterizedTypeTypeArguments :: ValidTypeClazz -> StateT ValidTypeClassData IO (V.Validation [TypeError] ())
getFieldInvalidParameterizedTypeTypeArguments ValidTypeClazz{..} = do
  foldM
    (\errorList field@ValidTypeField{..} -> do
      maybeError <- getInvalidParameterizedTypeTypeArguments (snd vfName) vfType
      return $ errorList <* maybeError)
    (pure ())
    vcFields

getMethodInvalidParameterizedTypeTypeArguments :: ValidTypeClazz -> StateT ValidTypeClassData IO (V.Validation [TypeError] ())
getMethodInvalidParameterizedTypeTypeArguments ValidTypeClazz{..} = do
  returnTypeErrors <- foldM
    (\errorList method@ValidTypeMethod{..} -> do
      maybeError <- getInvalidParameterizedTypeTypeArguments (snd vmName) vmType
      return $ errorList <* maybeError)
    (pure ())
    vcMethods
  foldM
    (\errorList method@ValidTypeMethod{..}  -> do
      newErrors <- foldM
        (\paramErrorList (ValidTypeParameter paramName paramType) -> do
          maybeParamErrors <- getInvalidParameterizedTypeTypeArguments (snd paramName) paramType
          return $ paramErrorList <* maybeParamErrors )
        (pure ())
        vmParams
      return $ errorList <* newErrors)
    returnTypeErrors
    vcMethods

getInvalidParameterizedTypeTypeArguments :: SourcePos ->
  TypeCheckerJavaType ->
  StateT ValidTypeClassData IO (V.Validation [TypeError] ())
getInvalidParameterizedTypeTypeArguments pos (TypeCheckerJavaReferenceType (TypeCheckerClassRefType crtw)) = do
  (TypeInfo ti) <- getClassTypeInfo' (getTypeCheckerClassReferenceTypeClassName crtw)
  let typeArgs = getTypeCheckerClassReferenceTypeTypeArguments crtw
  if null (getTypeParameters ti)
    then if not (null typeArgs)
      then return $ V.Failure [TypeError ("type "++show (getTypeName ti)++" does not take parameters") pos]
      else return $ V.Success ()
    else if length (getTypeParameters ti) /= length typeArgs
      then return $ V.Failure [TypeError ("wrong number of type arguments; required "++show (length (getTypeParameters ti))) pos]
      else do
        foldM 
          (\errorList paramArgPair -> do 
            newErrors <- isTypeArgumentWithinTypeParameterBounds pos paramArgPair
            return $ errorList <* newErrors) 
          (pure ())
          (zip (getTypeParameters ti) (VT.toList typeArgs))
getInvalidParameterizedTypeTypeArguments pos _ = return $ V.Success ()

isTypeArgumentWithinTypeParameterBounds :: SourcePos -> (TypeCheckerTypeParameter, TypeCheckerTypeArgument) -> StateT ValidTypeClassData IO (V.Validation [TypeError] ())
isTypeArgumentWithinTypeParameterBounds
  pos (
    TypeCheckerTypeParameter
      pname
        (Just (TypeCheckerClassTypeTypeBound boundClass boundInterfaces)),
    TypeCheckerTypeArgument _ argRtw) = do
  classBoundError <- ifM (isSubtypeOf argRtw (TypeCheckerClassRefType boundClass))
    (return $ V.Success ())
    (return $ V.Failure [TypeError ("type argument "++show argRtw++" is not within bounds of type varialbe "++show pname) pos])
  interfaceBoundErrors <- foldM 
    (\errorList interfaceBound ->
      ifM (isSubtypeOf argRtw (TypeCheckerClassRefType interfaceBound))
        (return $ V.Success())
        (return $ V.Failure [TypeError ("type argument "++show argRtw++" is not within bounds of type varialbe "++show pname) pos]))
    (pure ())
    boundInterfaces
  return $ classBoundError <* interfaceBoundErrors
isTypeArgumentWithinTypeParameterBounds
  pos (
    TypeCheckerTypeParameter
      pname
      (Just (TypeCheckerTypeVariableTypeBound _)),
    TypeCheckerTypeArgument _ argRtw) = undefined
isTypeArgumentWithinTypeParameterBounds
  pos (
    TypeCheckerTypeParameter
      pname
        Nothing,
    TypeCheckerTypeArgument _ argRtw) = undefined

getDuplicateMethods :: ValidTypeClazz -> [TypeError]
getDuplicateMethods ValidTypeClazz {..} =
  snd $ foldr
    (\method@ValidTypeMethod {..} (methodMap, duplicateList) ->
      let (nm,pos) = vmName in
      (case Map.lookup nm methodMap of
        Nothing -> (Map.insert nm [vmParams] methodMap, duplicateList)
        Just paramsList -> if vmParams `elem` paramsList
          then (methodMap, TypeError ("Duplicate method: "++show (mapValidTypeMethodToSignature method)) pos:duplicateList)
          else (Map.update (\l -> Just (vmParams:l)) nm methodMap, duplicateList)))
    (Map.empty, [])
    vcMethods

getClassInheritenceCycleErrors :: ValidTypeClazz -> StateT ValidTypeClassData IO [TypeError]
getClassInheritenceCycleErrors clazz = getClassInheritenceCycleErrors' clazz []

getClassInheritenceCycleErrors' :: ValidTypeClazz -> [TypeCheckerValidTypeQualifiedNameWrapper] -> StateT ValidTypeClassData IO [TypeError]
getClassInheritenceCycleErrors' ValidTypeClazz {..} classes = do
  (_,classMap) <- get
  let (parent,pos) = vcParent
      parentName = getErasedTypeName parent
    in
      if parentName `elem` classes
        then return [TypeError ("Cyclic Inheritence: "++show vcName) pos]
        else if Map.member parentName classMap
          then getClassInheritenceCycleErrors' (classMap Map.! parentName) (parentName : classes)
          else return []

getTypedClazz :: ValidTypeClazz -> StateT ValidTypeClassData IO (V.Validation [TypeError] TypedClazz)
getTypedClazz cls@ValidTypeClazz {..} = do
  typedMethodList <- getMethodsTermTypeErrors cls
  let (parentClass,_) = vcParent
  let parentClassName = getErasedTypeName parentClass
  return $ NewTypedClazz (P.CPublic:vcAccessFlags) vcName parentClassName vcFields <$> typedMethodList

getMethodsTermTypeErrors :: ValidTypeClazz -> StateT ValidTypeClassData IO (V.Validation [TypeError] [TypedMethod])
getMethodsTermTypeErrors cls@ValidTypeClazz {..} =
  foldM (\l m -> do
    typedMethodV <- checkMethodTermType cls m
    return $ (:) <$> typedMethodV <*> l)
  (V.Success [])
  vcMethods

{-- Check whether the type of a mehtod's term matches the method's return type -}
checkMethodTermType :: ValidTypeClazz -> ValidTypeMethod -> StateT ValidTypeClassData IO (V.Validation [TypeError] TypedMethod)
checkMethodTermType cls@ValidTypeClazz {..} method@ValidTypeMethod {vmMaybeImpl=Nothing,..} = do
    let (methodName, _) = vmName
    return $ V.Success $ NewTypedMethod methodName (VT.toList vmParams) vmType Nothing
checkMethodTermType cls@ValidTypeClazz {..} method@ValidTypeMethod {vmMaybeImpl=Just ValidTypeMethodImplementation{..},..} = do
    typeData <- get
    let (methodName, pos) = vmName
    let methodEnvironment = createMethodEnvironment typeData cls method
    typedTermV <- runReaderT (getType vmiTerm) methodEnvironment
    case typedTermV of
      V.Failure tes -> return $ V.Failure tes
      V.Success typedTerm -> do
        let termType = getTypedTermType typedTerm
        case vmType of
          TypeCheckerJavaPrimitiveType _ ->
            if convertTypeCheckerJavaType vmType == getUnboxedType termType
              then do
                typedTermNarrowCastIfNecessary <- addNarrowingCast typedTerm (convertTypeCheckerJavaType vmType)
                return $ V.Success (NewTypedMethod methodName (VT.toList vmParams) vmType (Just (TypedMethodImpl typedTermNarrowCastIfNecessary)))
              else
                return $ V.Failure [TypeError ("Incorrect return type: "++show (getTypedTermType typedTerm)) pos]
          TypeCheckerJavaReferenceType rtw ->
            ifM (isSubtypeOf
                  (TypeCheckerClassRefType (getBoxedType termType))
                  rtw)
              (do
                typedTermNarrowCastIfNecessary <- addNarrowingCast typedTerm (convertTypeCheckerJavaType vmType)
                return $ V.Success
                  (NewTypedMethod
                    methodName
                    (VT.toList vmParams)
                    vmType
                    (Just (TypedMethodImpl typedTermNarrowCastIfNecessary))))
              (return $ V.Failure [TypeError ("Incorrect return type: "++show (getTypedTermType typedTerm)) pos])
checkMethodTermType cls@ValidTypeClazz {..} method@ValidTypeMethod {vmMaybeImpl=Just ValidTypeConstructorImplementation{..},..} = do
  typeData <- get
  let constructorRightEnvironment = createConstructorEnvironmentRight typeData cls method
  let constructorLeftEnvironment = createConstructorEnvironmentLeft typeData cls
  eitherTypedConstructorInvocation <- case vmiConstructorInvocation of
    Left thisCI -> do
      typedCI <- runReaderT (getTypedConstructorInvocation cls thisCI) constructorRightEnvironment
      return $ Left typedCI
    Right superCI -> do
      typedCI <- runReaderT (getTypedSuperConstructorInvocation cls superCI) constructorRightEnvironment
      return $ Right typedCI
  typedAssignmentsV <- sequenceA <$> mapM (getAssignmentTypeError constructorLeftEnvironment constructorRightEnvironment) vmiAssignments
  case eitherTypedConstructorInvocation of
    Left typedThisCIV -> do
      let tupleV = (,) <$> typedThisCIV <*> typedAssignmentsV
      case tupleV of
        V.Failure tes -> return $ V.Failure tes
        V.Success (typedThisCI, typedAssignments) -> return $ V.Success
          (NewTypedMethod P.createNameInit (VT.toList vmParams) CP.createValidTypeJavaTypeObject (Just (TypedConstructorImpl typedThisCI typedAssignments)))
    Right typedSuperCIV -> do
      let tupleV = (,) <$> typedSuperCIV <*> typedAssignmentsV
      case tupleV of
        V.Failure tes -> return $ V.Failure tes
        V.Success (typedSuperCI,typedAssignments) -> return $ V.Success
          (NewTypedMethod P.createNameInit (VT.toList vmParams) CP.createValidTypeJavaTypeObject (Just (TypedConstructorImpl typedSuperCI typedAssignments)))

defaultConstructorInvocation :: TypeCheckerValidTypeQualifiedNameWrapper -> TypedConstructorInvocation
defaultConstructorInvocation parentCls = NewTypedConstructorInvocation parentCls [] []

getAbstractClassSubClassErrors :: ValidTypeClazz -> StateT ValidTypeClassData IO [TypeError]
getAbstractClassSubClassErrors cls = do
  either <- runExceptT $ getAbstractClassSubClassErrors' cls
  case either of
    Left errors -> return errors
    Right _ -> return []

getAbstractClassSubClassErrors' :: ValidTypeClazz -> ExceptT [TypeError] (StateT ValidTypeClassData IO) ()
getAbstractClassSubClassErrors' cls@ValidTypeClazz {..} =
  if P.CAbstract `elem` vcAccessFlags
    then return ()
    else do
      classTI@(TypeInfo ti) <- lift $ getClassTypeInfo' vcName
      parentClasses <- lift $ getOrderedParentTypes (fst vcParent)
      lift $ lift $ print ("parentClasses "++show parentClasses)
      parentClassesTI <- lift $ mapM getClassTypeInfo parentClasses
      reducedMethods <- lift $
        List.foldM
          combineMethodDeclList
          ([],Map.empty)
          (classTI:parentClassesTI)
      --lift $ lift $ print ("reducedMethods "++show vcName++show reducedMethods)
      let abstractMethods = filter
            (\(MethodDeclarationWithClassName md@(MethodDeclaration m) methodClassVtqnw,_,_) ->
              maAbstract (getMethodAttributes m))
            (fst reducedMethods)
      if null abstractMethods
        then return ()
        else
          let (MethodDeclarationWithClassName md methodClassVtqnw,ms,_) = head abstractMethods
              errorClassName = show methodClassVtqnw
              errorMethod = show ms
          in
            throwE [TypeError
              (show(getTypeName ti)++" is not abstract and does not override abstract method "++errorMethod++" in "++errorClassName) vcSourcePos]


data MethodDeclarationWithClassName = MethodDeclarationWithClassName MethodDeclaration TypeCheckerValidTypeQualifiedNameWrapper

combineMethodDeclList :: ([(MethodDeclarationWithClassName,MethodSignature,Type)],TypeParamEnvironment) ->
  TypeInfo ->
  (StateT ValidTypeClassData IO) ([(MethodDeclarationWithClassName,MethodSignature,Type)],TypeParamEnvironment)
combineMethodDeclList (list,env) clazzTi@(TypeInfo tp) = do
  let tpList = getTypeMethods tp
  let parentCrtw@(TypeCheckerClassReferenceTypeWrapper parentVtqnw maybeParentTypeArgs) = getTypeParent tp
  parentTypeInfo@(TypeInfo parentTi) <- getClassTypeInfo' parentVtqnw
  let parentEnv = buildTypeParamEnvironment
        (getTypeParameters parentTi)
        (Maybe.fromMaybe VT.empty maybeParentTypeArgs)
  tpMethodSigList <- mapM
    (\md@(MethodDeclaration m) ->
      (,,) (MethodDeclarationWithClassName md (getTypeName tp))
        <$> (MethodSignature (getMethodName m)
          <$> getSignatureWithResolvedTypeParams (getTypeName tp) env [] md)
        <*> getMethodTypeWithResolvedTypeParams (getTypeName tp) env [] md)
    tpList
  return (List.unionBy methodSigEq list tpMethodSigList,parentEnv)

methodSigEq :: (a,MethodSignature,Type) -> (a,MethodSignature,Type) ->  Bool
methodSigEq (_,ms1,_) (_,ms2,_) = ms1 == ms2

getNonReturnTypeSubstitutableOverrideErrors :: ValidTypeClazz -> StateT ValidTypeClassData IO [TypeError]
getNonReturnTypeSubstitutableOverrideErrors cls = do
  either <- runExceptT $ getNonReturnTypeSubstitutableOverrideErrors' cls
  case either of
    Left errors -> return errors
    Right _ -> return []

getNonReturnTypeSubstitutableOverrideErrors' :: ValidTypeClazz -> ExceptT [TypeError] (StateT ValidTypeClassData IO) ()
getNonReturnTypeSubstitutableOverrideErrors' cls@ValidTypeClazz {..} = do
  parentClasses <- lift $ getOrderedParentTypes (fst vcParent)
  parentClassesTI <- lift $ mapM getClassTypeInfo parentClasses
  let parentCrtw@(TypeCheckerClassReferenceTypeWrapper parentVtqnw maybeParentTypeArgs) = getTypeParent cls
  parentTypeInfo@(TypeInfo parentTi) <- lift $ getClassTypeInfo' parentVtqnw
  let parentEnv = buildTypeParamEnvironment
        (getTypeParameters parentTi)
        (Maybe.fromMaybe VT.empty maybeParentTypeArgs)
  reducedMethods <- lift $
    List.foldM
      combineMethodDeclList
      ([],parentEnv)
      parentClassesTI
  let nonConstructorMethods = filter (\ValidTypeMethod {..} -> fst vmName /= P.createNameInit) vcMethods
  errorList <- lift $ foldM (\errors m -> (errors++) <$> isMethodOverrideNotReturnTypeSubstitutable (fst reducedMethods) m) [] nonConstructorMethods
  case errorList of
    [] -> return ()
    list -> throwE list

isMethodOverrideNotReturnTypeSubstitutable :: [(MethodDeclarationWithClassName,MethodSignature,Type)] ->
  ValidTypeMethod ->
  StateT ValidTypeClassData IO [TypeError]
isMethodOverrideNotReturnTypeSubstitutable superClassMethods method@ValidTypeMethod {..} = do
  let (methodName,pos) = vmName
  let sig = mapValidTypeMethodToSignature method
  let possibleOverrideList = filter (\(_,methodSig,_) -> sig == methodSig) superClassMethods
  case possibleOverrideList of
    [] -> return []
    (MethodDeclarationWithClassName md@(MethodDeclaration m) methodClassVtqnw,sig,rt):_ -> do
      let errorMethod = show rt++" "++show sig
      let errorClass = show methodClassVtqnw
      if not (isTypeSupported rt)
        then return [TypeError "Method override of unsupported primitive return type" pos]
        else
          case vmType of
            TypeCheckerJavaPrimitiveType _ ->
              if convertTypeCheckerJavaType vmType == getUnboxedType rt
                then
                  return []
                else
                  return [TypeError ("cannot override "++errorMethod++" in "++errorClass++" return type is not compatible") pos]
            TypeCheckerJavaReferenceType rtw ->
              ifM (isSubtypeOf rtw (TypeCheckerClassRefType (getBoxedType rt)))
                (return [])
                (return [TypeError ("cannot override "++errorMethod++" in "++errorClass++" return type is not compatible") pos])

getAssignmentTypeError :: Environment -> Environment -> ValidTypeAssignment ->
                          (StateT ValidTypeClassData IO) (V.Validation [TypeError] TypedAssignment)
getAssignmentTypeError lenv renv ValidTypeAssignment {..} = do
  typeData <- get
  leftTermTypeV <- runReaderT (getType vaLeftHandTerm) lenv
  rightTermTypeV <- runReaderT (getType vaRightHandTerm) renv
  let termTupleV = (,) <$> leftTermTypeV <*> rightTermTypeV
  case termTupleV of
    V.Failure tes -> return $ V.Failure tes
    V.Success (leftTermType,rightTermType) -> do
      isSubtype <- isSubtypeOf (TypeCheckerClassRefType (getBoxedType (getTypedTermType rightTermType))) (TypeCheckerClassRefType (getBoxedType (getTypedTermType leftTermType)))
      if isTermValidForLeftAssignment vaLeftHandTerm && isSubtype
        then return $ V.Success (NewTypedAssignment leftTermType rightTermType)
        else return $ V.Failure [TypeError ("incompatible types: "++
            show (getTypedTermType rightTermType)++
            " cannot be converted to "++
            show (getTypedTermType leftTermType))
          (getValidTypeTermPosition vaRightHandTerm)]

isTermValidForLeftAssignment :: ValidTypeTerm -> Bool
isTermValidForLeftAssignment (ValidTypeApplication (ValidTypeApplicationTargetTerm (ValidTypeValue (ValidTypeVariable _ target))) (ValidTypeFieldAccess _ _)) = P.createNameThis == target
isTermValidForLeftAssignment (ValidTypeApplication (ValidTypeApplicationTargetTerm t) (ValidTypeFieldAccess _ _)) = isTermValidForLeftAssignment t
isTermValidForLeftAssignment t = False

getTypedConstructorInvocation ::  ValidTypeClazz ->
                                  ValidTypeConstructorInvocation ->
                                  ReaderT Environment (StateT ValidTypeClassData IO) (V.Validation [TypeError] TypedConstructorInvocation)
getTypedConstructorInvocation  cls@ValidTypeClazz {..} (ValidTypeConstructorInvocation pos terms) = do
  constructorSuperInvocationEnvironment <- ask
  typedTermsV <- sequenceA <$> mapM getType terms
  case typedTermsV of
    V.Failure tes -> return $ V.Failure tes
    V.Success typedTerms -> do
      let signature = MethodSignature init' (fmap getTypedTermType typedTerms)
      let crtw = TypeCheckerClassReferenceTypeWrapper
                   vcName
                   Nothing
      eitherThisConstructor <- lift $ getMethodDeclaration crtw signature []
      case eitherThisConstructor of
        Left errStr -> return $ V.Failure [TypeError ("No invocation compatible constructor: "++show vcName++"."++show signature) pos]
        Right (MethodDeclaration m) ->
          return $ V.Success (NewTypedConstructorInvocation vcName (getMethodParams m) typedTerms)

getTypedSuperConstructorInvocation ::  ValidTypeClazz ->
                                       ValidTypeSuperConstructorInvocation ->
                                       ReaderT Environment (StateT ValidTypeClassData IO) (V.Validation [TypeError] TypedConstructorInvocation)
getTypedSuperConstructorInvocation  cls@ValidTypeClazz {..} (ValidTypeSuperConstructorInvocation pos terms) = do
  constructorSuperInvocationEnvironment <- ask
  typedTermsV <- sequenceA <$> mapM getType terms
  case typedTermsV of
    V.Failure tes -> return $ V.Failure tes
    V.Success typedTerms -> do
      let (parentCrtw, _) = vcParent
      let parentClassName = getErasedTypeName parentCrtw
      let signature = MethodSignature init' (fmap getTypedTermType typedTerms)
      eitherSuperConstructor <- lift $ getMethodDeclaration parentCrtw signature []
      case eitherSuperConstructor of
        Left errStr -> return $ V.Failure [TypeError ("No invocation compatible constructor: "++show vcName++"."++show signature) pos]
        Right (MethodDeclaration m) ->
          return $ V.Success (NewTypedConstructorInvocation parentClassName (getMethodParams m) typedTerms)

getConstructorsUnassignedFieldErrors :: ValidTypeClazz -> StateT ValidTypeClassData IO [TypeError]
getConstructorsUnassignedFieldErrors cls@ValidTypeClazz {..} = do
  let constructors = filter (\ValidTypeMethod {..} -> fst vmName == P.createNameInit)  vcMethods
  return $ foldr (\c list -> getConstructorUnassignedFieldError cls c ++ list) [] constructors

getConstructorUnassignedFieldError :: ValidTypeClazz -> ValidTypeMethod -> [TypeError]
getConstructorUnassignedFieldError cls@ValidTypeClazz {..}
                                   constructor@ValidTypeMethod {vmMaybeImpl=(Just ValidTypeConstructorImplementation {..}),..} =
  let hasThis = case vmiConstructorInvocation of
        (Left _) -> True
        _ -> False
      fieldSet = Set.fromList (fmap (\ValidTypeField {..} -> fst vfName) vcFields)
      assignedFieldSet = Set.fromList (mapMaybe (\ValidTypeAssignment {..} -> getAssignmentTermField vaLeftHandTerm) vmiAssignments)
      unassignedFieldSet = trace (show fieldSet++":"++show assignedFieldSet) $ Set.difference fieldSet assignedFieldSet
  in
      [TypeError ("Constructor does not assign values to all fields: "++show (mapValidTypeMethodToSignature constructor)) (snd vmName) | not hasThis && Set.size unassignedFieldSet /= 0]
getConstructorUnassignedFieldError cls@ValidTypeClazz {..}
                                   constructor@ValidTypeMethod {vmMaybeImpl=(Just ValidTypeMethodImplementation {..}),..} = []
getConstructorUnassignedFieldError cls@ValidTypeClazz {..}
                                   constructor@ValidTypeMethod {vmMaybeImpl=Nothing,..} = []

getAssignmentTermField :: ValidTypeTerm -> Maybe P.SimpleName
getAssignmentTermField (ValidTypeApplication (ValidTypeApplicationTargetTerm (ValidTypeValue (ValidTypeVariable _ target))) (ValidTypeFieldAccess _ fieldName)) = if target == P.createNameThis then Just fieldName else Nothing
getAssignmentTermField (ValidTypeApplication (ValidTypeApplicationTargetTerm innerApplication@(ValidTypeApplication _ _)) _) = getAssignmentTermField innerApplication
getAssignmentTermField _ = Nothing

leastUpperBound :: [TypeCheckerClassReferenceTypeWrapper] -> StateT ValidTypeClassData IO Type
leastUpperBound typeList = do
  st <- mapM getOrderedParentTypes typeList
  let ec = List.nub (List.foldl' List.intersect [] st)
  maybeLub <-foldM (\mec tp -> case mec of
                            Nothing -> return $ Just tp
                            Just tp' -> ifM (isSubtypeOf (TypeCheckerClassRefType tp) (TypeCheckerClassRefType tp')) (return (Just tp)) (return (Just tp')))
    Nothing
    ec
  case maybeLub of
    Nothing -> return $ L CP.createValidTypeClassTypeObject
    Just lub -> return $ L lub

getFieldDeclaration :: TypeInfo -> P.SimpleName -> StateT ValidTypeClassData IO (Maybe FieldDeclaration)
getFieldDeclaration ti@(TypeInfo t) nm = do
  let maybeFd = getTypeFieldDeclaration t nm
  case maybeFd of
    Just fd -> return $ Just fd
    Nothing ->
      if getTypeName t == getErasedTypeName CP.createValidTypeClassTypeObject
        then return Nothing
        else do
          parentType <- getClassTypeInfo (getTypeParent t)
          getFieldDeclaration parentType nm

getConstructorDeclaration :: TypeCheckerClassReferenceTypeWrapper -> [Type] -> [TypeCheckerTypeArgument] -> StateT ValidTypeClassData IO (Either String MethodDeclaration)
getConstructorDeclaration crtw@(TypeCheckerClassReferenceTypeWrapper vtqnw _) argumentTypes methodTypeArgs= do
  consList <- getApplicableConstructors crtw argumentTypes methodTypeArgs
  case consList of
    [] -> return $ Left ("no suitable constructor found for "++show vtqnw++"("++List.intercalate "," (fmap show argumentTypes)++")")
    _ -> do
      result <- getMostSpecificMethod crtw methodTypeArgs consList
      case result of
        Nothing -> return $ Left ("reference to "++show vtqnw++" is ambiguous")
        Just constructor -> return $ Right constructor

{--
Resolve an appropriate method for a method invocation expression (MethodSignature).
Logic derived from JLS 15.12
-}
getMethodDeclaration :: TypeCheckerClassReferenceTypeWrapper -> MethodSignature -> [TypeCheckerTypeArgument] -> StateT ValidTypeClassData IO (Either String MethodDeclaration)
getMethodDeclaration crtw signature@(MethodSignature nm _) methodTypeArgs= do
  mdList <- getApplicableMethods crtw signature methodTypeArgs
  case mdList of
    [] -> return $ Left ("no suitable method found for "++show signature)
    _ -> do
      result <- getMostSpecificMethod crtw methodTypeArgs mdList
      case result of
        Nothing -> return $ Left ("reference to "++show nm++" is ambiguous")
        Just md -> return $ Right md

getStaticMethodDeclaration :: TypeCheckerValidTypeQualifiedNameWrapper -> MethodSignature -> [TypeCheckerTypeArgument] -> StateT ValidTypeClassData IO (Either String MethodDeclaration)
getStaticMethodDeclaration vtqnw signature@(MethodSignature nm _) methodTypeArgs = do
  mdList <- getApplicableStaticMethods vtqnw signature methodTypeArgs
  case mdList of
    [] -> return $ Left ("no suitable method found for "++show signature)
    _ -> do
      result <- getMostSpecificMethod (TypeCheckerClassReferenceTypeWrapper vtqnw Nothing) methodTypeArgs mdList
      case result of
        Nothing -> return $ Left ("reference to "++show nm++" is ambiguous")
        Just md -> return $ Right md

{--
Given a list of class methods, select the method that is most specific. The list of methods will be the result of a selction
process in which potentially applicable methods for a given method invocation are selected. Logic derived form JLS 15.12.2.5
-}
getMostSpecificMethod :: TypeCheckerClassReferenceTypeWrapper -> [TypeCheckerTypeArgument] -> [MethodDeclaration] -> StateT ValidTypeClassData IO (Maybe MethodDeclaration)
getMostSpecificMethod crtw@(TypeCheckerClassReferenceTypeWrapper vtqnw _) methodTypeArgs mdList = do
  foldM
    foldFunc
    Nothing
    mdList
  where
    foldFunc result md =
      case result of
        r@(Just _) -> return r -- once a most specific method has been found, we are done
        Nothing -> do
          ifM (isMostSpecific md) (return (Just md)) (return Nothing)
    isMostSpecific md =
      and <$> mapM
        (\candidate ->
          ifM
            (isMethodApplicableByLooseInvocation' crtw candidate md)
            (return True)
            (return False))
        mdList
    isMethodApplicableByLooseInvocation' :: TypeCheckerClassReferenceTypeWrapper -> MethodDeclaration -> MethodDeclaration -> StateT ValidTypeClassData IO Bool
    isMethodApplicableByLooseInvocation' crtw@(TypeCheckerClassReferenceTypeWrapper _ maybeTypeArguments) md md'@(MethodDeclaration m') = do
      (TypeInfo ti) <- getClassTypeInfo crtw
      let paramaterizedTypeEnvMap = case maybeTypeArguments of
            Nothing -> Map.empty
            Just typeArgs -> buildTypeParamEnvironment (getTypeParameters ti) typeArgs
      ms <- MethodSignature (getMethodName m') <$> getSignatureWithResolvedTypeParams vtqnw paramaterizedTypeEnvMap methodTypeArgs md'
      isMethodApplicableByLooseInvocation vtqnw paramaterizedTypeEnvMap ms methodTypeArgs md

getApplicableConstructors :: TypeCheckerClassReferenceTypeWrapper -> [Type] -> [TypeCheckerTypeArgument] -> StateT ValidTypeClassData IO [MethodDeclaration]
getApplicableConstructors crtw@(TypeCheckerClassReferenceTypeWrapper vtqnw maybeTypeArguments) argumentTypes methodTypeArgs = do
  tiw@(TypeInfo ti) <- getClassTypeInfo crtw
  let typeParameters = getTypeParameters ti
  let paramaterizedTypeEnvMap = case maybeTypeArguments of
        Nothing -> Map.empty
        Just typeArgs -> buildTypeParamEnvironment typeParameters typeArgs
  pams <- getPotentiallyApplicableConstructors tiw argumentTypes
  filterM
    (isMethodApplicableByLooseInvocation vtqnw paramaterizedTypeEnvMap (MethodSignature init' argumentTypes) methodTypeArgs)
    pams

getApplicableMethods :: TypeCheckerClassReferenceTypeWrapper -> MethodSignature -> [TypeCheckerTypeArgument] -> StateT ValidTypeClassData IO [MethodDeclaration]
getApplicableMethods crtw@(TypeCheckerClassReferenceTypeWrapper vtqnw maybeTypeArguments) signature methodTypeArgs = do
  tiw@(TypeInfo ti) <- getClassTypeInfo crtw
  let !z = trace("type args: "++show maybeTypeArguments) 1
  let typeParameters = getTypeParameters ti
  let paramaterizedTypeEnvMap = case maybeTypeArguments of
        Nothing -> Map.empty
        Just typeArgs -> buildTypeParamEnvironment typeParameters typeArgs
  pams <- getPotentiallyApplicableMethods tiw signature
  filterM
    (isMethodApplicableByLooseInvocation vtqnw paramaterizedTypeEnvMap signature methodTypeArgs)
    pams

getApplicableStaticMethods :: TypeCheckerValidTypeQualifiedNameWrapper -> MethodSignature -> [TypeCheckerTypeArgument] -> StateT ValidTypeClassData IO [MethodDeclaration]
getApplicableStaticMethods vtqnw signature methodTypeArgs = do
  (TypeInfo ti) <- getClassTypeInfo' vtqnw
  pams <- getTypePotentiallyApplicableMethods ti signature
  filterM
    (isMethodApplicableByLooseInvocation vtqnw Map.empty signature methodTypeArgs)
    (filter (\(MethodDeclaration m) -> maStatic (getMethodAttributes m)) pams)

isMethodApplicableByLooseInvocation :: TypeCheckerValidTypeQualifiedNameWrapper ->
                                       TypeParamEnvironment ->
                                       MethodSignature ->
                                       [TypeCheckerTypeArgument] ->
                                       MethodDeclaration ->
                                       StateT ValidTypeClassData IO Bool
isMethodApplicableByLooseInvocation vtqnw classParamaterizedTypeEnvMap signature@(MethodSignature searchName searchParams) methodTypeArgs md@(MethodDeclaration m) = do
    let methodTypeParams = getMethodTypeParameters m
    let parameterizedTypeEnvMap = Map.union
          classParamaterizedTypeEnvMap
          (buildTypeParamEnvironment methodTypeParams methodTypeArgs)
    let !z = trace ("signature: "++show signature++"--"++show parameterizedTypeEnvMap) 1
    substitutedParams <- getSignatureWithResolvedTypeParams vtqnw parameterizedTypeEnvMap methodTypeArgs md
    let !z' = trace ("env:"++show substitutedParams) 1
    areParametersInvocationCompatible (fmap (L . getBoxedType) searchParams) substitutedParams
  where
    areParametersInvocationCompatible :: [Type] -> [Type] -> StateT ValidTypeClassData IO Bool
    areParametersInvocationCompatible sigParamTypes candidateParams = do
      result <- foldM (\r (ptp, candidatetp) ->
        (r &&) <$> isTypeInvocationCompatible ptp candidatetp)
        True
        (zip sigParamTypes candidateParams)
      let !x = trace ("areParametersInvocationCompatible "++show sigParamTypes++" - "++show candidateParams++" -> "++show result) 1
      return result

    isTypeInvocationCompatible :: Type -> Type -> StateT ValidTypeClassData IO Bool
    isTypeInvocationCompatible (L baseType) I = isSubtypeOf (TypeCheckerClassRefType baseType) CP.createValidTypeRefTypeInteger
    isTypeInvocationCompatible (L baseType) Z = isSubtypeOf (TypeCheckerClassRefType baseType) CP.createValidTypeRefTypeBoolean
    isTypeInvocationCompatible (L baseType) (L vtn) = isSubtypeOf (TypeCheckerClassRefType baseType) (TypeCheckerClassRefType vtn)
    isTypeInvocationCompatible _ _ = return False

getPotentiallyApplicableConstructors :: TypeInfo ->
                                        [Type] ->
                                        StateT ValidTypeClassData IO [MethodDeclaration]
getPotentiallyApplicableConstructors t@(TypeInfo ti) consArguments =
    getTypePotentiallyApplicableMethods ti (MethodSignature init' consArguments)

{--
A class or interface (parameter 1) determined by compile-time step 1 (§15.12.1) is searched
for all member methods that are potentially applicable to method invocation (parameter 2);
members inherited from superclasses and superinterfaces are included in this search.
-}
getPotentiallyApplicableMethods :: TypeInfo ->
                                   MethodSignature ->
                                   StateT ValidTypeClassData IO [MethodDeclaration]
getPotentiallyApplicableMethods t@(TypeInfo ti) methodSig = do
  pams <- getPotentiallyApplicableMethods' [] t methodSig
  let !x = trace ("getPotentiallyApplicableMethods@@" ++show (getTypeName ti)++"."++show methodSig++" = "++show (fmap (\(_,MethodDeclaration m) -> show m) pams)) 1
  return $ fmap snd pams


getPotentiallyApplicableMethods' :: [(MethodSignature,MethodDeclaration)] ->
                                    TypeInfo ->
                                    MethodSignature ->
                                    StateT ValidTypeClassData IO [(MethodSignature,MethodDeclaration)]
getPotentiallyApplicableMethods' mdList ti@(TypeInfo t) sig = do
  mdList' <- getTypePotentiallyApplicableMethods t sig
  let classTypeParameters = getTypeParameters t
  let mdList'' =
        List.foldr (\md l ->
          if any (\(methodSig,_) -> methodSig == getErasedMethodSignature classTypeParameters md) l
            then l
            else (getErasedMethodSignature classTypeParameters md,md):l)
          mdList
          mdList'
  if getTypeName t == getErasedTypeName CP.createValidTypeClassTypeObject
    then
      return mdList''
    else do
      parentType <- getClassTypeInfo (getTypeParent t)
      mdList''' <- foldM
        (\l interfaceCtrw ->
          join (getPotentiallyApplicableMethods' l <$> getClassTypeInfo interfaceCtrw <*> return sig))
        mdList''
        (getTypeImplements t)
      getPotentiallyApplicableMethods' mdList''' parentType sig

object :: T.Text
object = T.pack "java/lang/Object"
rparens = T.pack ")"
semi = T.pack ";"

mapValidTypeMethodToSignature :: ValidTypeMethod -> MethodSignature
mapValidTypeMethodToSignature method@ValidTypeMethod {..} =
  let (mname, _) = vmName
  in
    MethodSignature mname (VT.toList (fmap mapParameterToType vmParams))

mapParameterToType :: ValidTypeParameter -> Type
mapParameterToType ValidTypeParameter {..} = convertTypeCheckerJavaType vpType

isConcreteClass :: TypeCheckerClassReferenceTypeWrapper -> StateT ValidTypeClassData IO Bool
isConcreteClass tp = do
  (TypeInfo typeInfo) <- getClassTypeInfo tp
  return $ not (caAbstract (getTypeAccessFlags typeInfo))

isInterface :: TypeCheckerClassReferenceTypeWrapper -> StateT ValidTypeClassData IO Bool
isInterface tp = do
  (TypeInfo typeInfo) <- getClassTypeInfo tp
  return $ caInterface (getTypeAccessFlags typeInfo)

isTypeBoolean :: Type -> Bool
isTypeBoolean Z = True
isTypeBoolean _ = False

isTypeInteger :: Type -> Bool
isTypeInteger I = True
isTypeInteger _ = False

getBoxedType :: Type -> TypeCheckerClassReferenceTypeWrapper
getBoxedType I = CP.createValidTypeClassTypeInteger
getBoxedType Z = CP.createValidTypeClassTypeBoolean
getBoxedType tp@(L vtn) = vtn
getBoxedType t = trace ("getBoxedType with invalid type: "++show t) undefined

getUnboxedType :: Type -> Type
getUnboxedType (L vtn) | vtn == CP.createValidTypeClassTypeBoolean = Z
                       | vtn == CP.createValidTypeClassTypeInteger = I
getUnboxedType t = t

{-- First parameter will be includeded in the list -}
getOrderedParentTypes :: TypeCheckerClassReferenceTypeWrapper -> StateT ValidTypeClassData IO [TypeCheckerClassReferenceTypeWrapper]
getOrderedParentTypes crtw = do
  listWithoutObject <- unfoldrM
      (\crtw' ->
        fmap
          (\(TypeInfo ti) -> if crtw' == CP.createValidTypeClassTypeObject
                            then Nothing
                            else Just (crtw', getTypeParent ti))
          (getClassTypeInfo crtw'))
      crtw
  return $ reverse (CP.createValidTypeClassTypeObject:reverse listWithoutObject)

buildTypeParamEnvironment :: (Foldable f, Foldable g) => f TypeCheckerTypeParameter -> g TypeCheckerTypeArgument -> TypeParamEnvironment
buildTypeParamEnvironment genericTypeParams typeArgs =
  Map.fromList
    (zip
      (fmap
        (\(TypeCheckerTypeParameter paramName _) -> paramName)
        (F.toList genericTypeParams))
      (fmap
        (\(TypeCheckerTypeArgument _ rtw) -> rtw)
        (F.toList typeArgs)))

getDirectSupertypeSet :: TypeCheckerReferenceTypeWrapper -> StateT ValidTypeClassData IO (Set.Set TypeCheckerReferenceTypeWrapper)
getDirectSupertypeSet(TypeCheckerClassRefType refType) | CP.createValidTypeClassTypeObject == refType = return Set.empty
getDirectSupertypeSet(TypeCheckerClassRefType refType@(TypeCheckerClassReferenceTypeWrapper vtqnw maybeTypeArgs)) = do
  (TypeInfo ti) <- getClassTypeInfo' vtqnw
  let refTypeTypeParams = getTypeParameters ti
  let parentCrtw@(TypeCheckerClassReferenceTypeWrapper parentVtqnw maybeParentTypeArgs) = getTypeParent ti
  let typeParamEnv = case maybeTypeArgs of
        Nothing -> Map.empty
        Just typeArgs -> buildTypeParamEnvironment refTypeTypeParams typeArgs
  let substitutedParentCrtw = case maybeParentTypeArgs of
        Nothing -> parentCrtw
        Just typeArgs ->
          TypeCheckerClassReferenceTypeWrapper
            parentVtqnw
            (Just (VT.fromList (substituteTypeArgs typeArgs typeParamEnv)))
  let interfaceCrtw = getTypeImplements ti
  let substitutedInterfaceCrtw =
        fmap
          (\interfaceCrtw'@(TypeCheckerClassReferenceTypeWrapper interfaceVtqnw maybeInterfaceTypeArgs) ->
            case maybeInterfaceTypeArgs of
              Nothing -> interfaceCrtw'
              Just typeArgs ->
                TypeCheckerClassReferenceTypeWrapper
                  interfaceVtqnw
                  (Just (VT.fromList (substituteTypeArgs typeArgs typeParamEnv))))
          interfaceCrtw
  return $ Set.fromList $ fmap TypeCheckerClassRefType (substitutedParentCrtw:substitutedInterfaceCrtw)
getDirectSupertypeSet _ = undefined

{-- Supertype set is the reflexive and transitive closure over the direct supertype relation (getDirectSupertypeSet)
-}
getSupertypeSet :: TypeCheckerReferenceTypeWrapper -> StateT ValidTypeClassData IO (Set.Set TypeCheckerReferenceTypeWrapper)
getSupertypeSet refType = do
  directSupertypeSet <- getDirectSupertypeSet refType
  foldM
    (\supertypeSet refType' -> Set.union supertypeSet <$> getSupertypeSet refType')
    directSupertypeSet
    directSupertypeSet

isSubtypeOf :: TypeCheckerReferenceTypeWrapper -> TypeCheckerReferenceTypeWrapper -> StateT ValidTypeClassData IO Bool
isSubtypeOf childRtw parentRtw = do
  let sts = getSupertypeSet childRtw
  let stsContainsParent =
        anyM (containsReferenceType parentRtw) . Set.toList =<< sts
  let parentContainsChild = containsReferenceType parentRtw childRtw
  (||) <$> parentContainsChild <*> stsContainsParent

containsReferenceType :: TypeCheckerReferenceTypeWrapper -> TypeCheckerReferenceTypeWrapper -> StateT ValidTypeClassData IO Bool
containsReferenceType crt1@(TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper _ Nothing))
                      crt2@(TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper _ _)) = return (crt1 == crt2)
containsReferenceType crt1@(TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper _ _))
                      crt2@(TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper _ Nothing)) = return (crt1 == crt2)
containsReferenceType (TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper vtqnw1 (Just typeArgs1)))
                      (TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper vtqnw2 (Just typeArgs2))) = do
  let sameClassName = vtqnw1 == vtqnw2
  typeArgsContain <- foldM
    (\accum (arg1, arg2) ->
      (accum &&) <$> containsTypeArgument arg1 arg2)
    True
    (zip (VT.toList typeArgs1) (VT.toList typeArgs2))
  return (sameClassName && typeArgsContain)
containsReferenceType crt1 crt2 = return (crt1 == crt2) -- TODO: until we support type variables and arrays

{-- Does T1 (first argument) contain T2 (second argument) See JLS 4.5.1 -}
containsTypeArgument :: TypeCheckerTypeArgument -> TypeCheckerTypeArgument -> StateT ValidTypeClassData IO Bool
containsTypeArgument (TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorExtends) t1Rtw)
                     (TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorExtends) t2Rtw) =
    isSubtypeOf t2Rtw t1Rtw

containsTypeArgument (TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorSuper) t1Rtw)
                     (TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorSuper) t2Rtw) =
    isSubtypeOf t1Rtw t2Rtw

containsTypeArgument (TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorExtends) createValidTypeRefTypeObject)
                     (TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorSuper) t2Rtw) =
    return True

containsTypeArgument (TypeCheckerTypeArgument Nothing t1Rtw)
                     (TypeCheckerTypeArgument Nothing t2Rtw) =
    return $ t1Rtw == t2Rtw

containsTypeArgument t1@(TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorExtends) t1Rtw)
                     t2@(TypeCheckerTypeArgument Nothing t2Rtw) =
    (t1Rtw == t2Rtw ||) <$> containsTypeArgument t1 (TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorExtends) t2Rtw)

containsTypeArgument t1@(TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorSuper) t1Rtw)
                     t2@(TypeCheckerTypeArgument Nothing t2Rtw) =
    (t1Rtw == t2Rtw ||) <$> containsTypeArgument t1 (TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorSuper) t2Rtw)

containsTypeArgument _ _ = return False

substituteTypeArgs :: (Foldable f) => f TypeCheckerTypeArgument -> TypeParamEnvironment -> [TypeCheckerTypeArgument]
substituteTypeArgs typeArgs env =
  fmap (`substituteTypeArgument` env) (F.toList typeArgs)

substituteTypeArgument :: TypeCheckerTypeArgument -> TypeParamEnvironment -> TypeCheckerTypeArgument
substituteTypeArgument (TypeCheckerTypeArgument wildcardIndicator (TypeCheckerClassRefType crtw@(TypeCheckerClassReferenceTypeWrapper _ _))) env =
  TypeCheckerTypeArgument
    wildcardIndicator
    (TypeCheckerClassRefType (substituteClassRefTypeTypeArgs crtw env))
substituteTypeArgument (TypeCheckerTypeArgument wildcardIndicator (TypeCheckerTypeVariableRefType typeVariable)) env =
  TypeCheckerTypeArgument
    wildcardIndicator
    (substituteTypeVariableRefType typeVariable env)
substituteTypeArgument (TypeCheckerTypeArgument wildcardIndicator (TypeCheckerArrayRefType rtw)) env =
  TypeCheckerTypeArgument
    wildcardIndicator
    (substituteArrayRefTypeTypeArg rtw env)

substituteClassRefTypeTypeArgs :: TypeCheckerClassReferenceTypeWrapper -> TypeParamEnvironment -> TypeCheckerClassReferenceTypeWrapper
substituteClassRefTypeTypeArgs rtw@(TypeCheckerClassReferenceTypeWrapper qn maybeTypeArgs) env =
  case maybeTypeArgs of
    Nothing -> rtw
    Just typeArgs ->
      TypeCheckerClassReferenceTypeWrapper qn (Just (fmap (\ta' -> substituteTypeArgument ta' env) typeArgs))

substituteTypeVariableRefType :: SimpleName -> TypeParamEnvironment -> TypeCheckerReferenceTypeWrapper
substituteTypeVariableRefType typeVariable env =
  case env Map.!? typeVariable of
    Nothing -> error ("undefined type variable: "++show typeVariable++" in "++show env)
    Just typeVariableResolvedRefType -> typeVariableResolvedRefType

substituteArrayRefTypeTypeArg :: TypeCheckerReferenceTypeWrapper -> TypeParamEnvironment -> TypeCheckerReferenceTypeWrapper
substituteArrayRefTypeTypeArg rtw env =
  case rtw of
    TypeCheckerClassRefType crtw@(TypeCheckerClassReferenceTypeWrapper _ _) ->
      TypeCheckerArrayRefType (TypeCheckerClassRefType (substituteClassRefTypeTypeArgs crtw env))
    TypeCheckerTypeVariableRefType sn ->
      substituteTypeVariableRefType sn env
    TypeCheckerArrayRefType rtw ->
      TypeCheckerArrayRefType (substituteArrayRefTypeTypeArg rtw env)

resolveTypeParams :: MethodDeclaration -> ReaderT TypeParamEnvironment (StateT ValidTypeClassData IO) [Type]
resolveTypeParams md@(MethodDeclaration m) =
  mapM
    resolveTypeParam
    (getMethodParams m)

resolveTypeParam :: Type -> ReaderT TypeParamEnvironment (StateT ValidTypeClassData IO) Type
resolveTypeParam t = do
  envMap <- ask
  case t of
    L crtw@(TypeCheckerClassReferenceTypeWrapper vtqnw (Just typeArgs)) -> return $
      L
        (TypeCheckerClassReferenceTypeWrapper
          vtqnw
          (Just (VT.fromList (substituteTypeArgs typeArgs envMap))));
    T sn -> case envMap Map.!? sn of
      Nothing -> error ("Undefined type variable: "++ show sn ++ " in " ++ show envMap)
      Just rtw -> case rtw of
        TypeCheckerClassRefType crtw@(TypeCheckerClassReferenceTypeWrapper vtqnw (Just typeArgs)) -> return $
          L
            (TypeCheckerClassReferenceTypeWrapper
              vtqnw
              (Just (VT.fromList (substituteTypeArgs typeArgs envMap))));
        TypeCheckerClassRefType crtw@(TypeCheckerClassReferenceTypeWrapper _ Nothing) -> return (L crtw)
        TypeCheckerTypeVariableRefType sn' -> return (T sn')
        TypeCheckerArrayRefType rtw -> return U
    _ -> return t

eraseTypeParams :: MethodDeclaration -> ReaderT TypeParamEnvironment (StateT ValidTypeClassData IO) [Type]
eraseTypeParams methodDeclaration@(MethodDeclaration m) = do
  let vtqnw = getMethodClassName m
  mapM
    (eraseTypeParam vtqnw)
    (getMethodParams m)

eraseTypeParam :: TypeCheckerValidTypeQualifiedNameWrapper -> Type -> ReaderT TypeParamEnvironment (StateT ValidTypeClassData IO) Type
eraseTypeParam vtqnw t = do
  (TypeInfo clazz) <- lift $ getClassTypeInfo' vtqnw
  return $ getErasedType (getTypeParameters clazz) t

getSignatureWithResolvedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> [TypeCheckerTypeArgument] -> MethodDeclaration -> StateT ValidTypeClassData IO [Type]
getSignatureWithResolvedTypeParams vtqnw env methodTypeArgs md@(MethodDeclaration m) = do
  let envWithMethodTypeArgs = Map.union env (buildTypeParamEnvironment (getMethodTypeParameters m) methodTypeArgs)
  maybeResolvedSig <- getMappedMethodDeclaration' resolveTypeParams vtqnw envWithMethodTypeArgs md
  case maybeResolvedSig of
    Just resolvedSig -> return resolvedSig
    Nothing -> error ("Unable to resolve type params in method signature: "++show vtqnw)

getSignatureWithErasedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> [TypeCheckerTypeArgument] -> MethodDeclaration -> StateT ValidTypeClassData IO [Type]
getSignatureWithErasedTypeParams vtqnw env methodTypeArgs md@(MethodDeclaration m) = do
  let envWithMethodTypeArgs = Map.union env (buildTypeParamEnvironment (getMethodTypeParameters m) methodTypeArgs)
  maybeResolvedSig <- getMappedMethodDeclaration' eraseTypeParams vtqnw envWithMethodTypeArgs md
  case maybeResolvedSig of
    Just resolvedSig -> return resolvedSig
    Nothing -> error ("Unable to erase type params in method signature: "++show vtqnw)

getMethodTypeWithResolvedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> [TypeCheckerTypeArgument]-> MethodDeclaration -> StateT ValidTypeClassData IO Type
getMethodTypeWithResolvedTypeParams vtqnw env methodTypeArgs md@(MethodDeclaration m) = do
  let envWithMethodTypeArgs = Map.union env (buildTypeParamEnvironment (getMethodTypeParameters m) methodTypeArgs)
  maybeResolvedType <- getMappedMethodDeclaration'
    (\md@(MethodDeclaration m) -> do
      let t = getMethodType m
      resolveTypeParam t)
    vtqnw
    envWithMethodTypeArgs
    md
  case maybeResolvedType of
    Just resolvedType -> return resolvedType
    Nothing -> error ("Unable to resolve type params in method signature: "++show vtqnw++" "++show md)

getMethodTypeWithErasedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> [TypeCheckerTypeArgument] -> MethodDeclaration -> StateT ValidTypeClassData IO Type
getMethodTypeWithErasedTypeParams vtqnw env methodTypeArgs md@(MethodDeclaration m) = do
  let envWithMethodTypeArgs = Map.union env (buildTypeParamEnvironment (getMethodTypeParameters m) methodTypeArgs)
  maybeResolvedType <- getMappedMethodDeclaration'
    (\md@(MethodDeclaration m) -> do
      let t = getMethodType m
      eraseTypeParam (getMethodClassName m) t)
    vtqnw
    envWithMethodTypeArgs
    md
  case maybeResolvedType of
    Just resolvedType -> return resolvedType
    Nothing -> error ("Unable to resolve type params in method signature: "++show vtqnw++" "++show md)

getMappedMethodDeclaration' ::  (MethodDeclaration ->
                                  ReaderT TypeParamEnvironment (StateT ValidTypeClassData IO) a) ->
                                TypeCheckerValidTypeQualifiedNameWrapper ->
                                TypeParamEnvironment ->
                                MethodDeclaration ->
                                StateT ValidTypeClassData IO (Maybe a)
getMappedMethodDeclaration' mapper vtqnw envMap methodDeclaration@(MethodDeclaration md) = do
  if vtqnw == getMethodClassName md
    then
      Just <$> runReaderT (mapper methodDeclaration) envMap
    else do
      (TypeInfo clazz) <- getClassTypeInfo' vtqnw
      let (TypeCheckerClassReferenceTypeWrapper parentVtqnw maybeParentTypeArgs) = getTypeParent clazz

      interfaceResolvedSig <- foldM
        (\l (TypeCheckerClassReferenceTypeWrapper interfaceVtqnw maybeInterfaceTypeArgs) -> do
          (TypeInfo interfaceClazz) <- getClassTypeInfo' interfaceVtqnw
          let interfaceEnv = case maybeInterfaceTypeArgs of
                Nothing -> Map.empty
                Just interfaceTypeArgs ->
                  let substitutedTypeArgs = substituteTypeArgs interfaceTypeArgs envMap
                  in
                    buildTypeParamEnvironment (getTypeParameters interfaceClazz) substitutedTypeArgs

          maybeResolvedSig <- getMappedMethodDeclaration' mapper interfaceVtqnw interfaceEnv methodDeclaration
          return $ case maybeResolvedSig of
            Nothing -> l
            Just resolvedSig -> Just resolvedSig)
        Nothing
        (getTypeImplements clazz)

      case interfaceResolvedSig of
        Just resolvedSig -> return $ Just resolvedSig
        Nothing -> do
          (TypeInfo parentClazz) <- getClassTypeInfo' parentVtqnw
          if getTypeName clazz /= CP.createValidTypeNameObject
            then do
              let parentEnv = case maybeParentTypeArgs of
                    Nothing -> Map.empty
                    Just parentTypeArgs ->
                      let substitutedParentTypeArgs = substituteTypeArgs parentTypeArgs envMap
                      in
                        buildTypeParamEnvironment (getTypeParameters parentClazz) substitutedParentTypeArgs
              getMappedMethodDeclaration' mapper parentVtqnw parentEnv methodDeclaration
            else
              return Nothing

{--  let fieldType = case getFieldType fd of
        I -> I
        Z -> Z
        U -> U
        L crtw -> L crtw
        T sn -> case envMap Map.!? sn of
          Nothing -> error ("Undefined type variable: "++ show sn ++ " in " ++ show envMap)
          Just rtw -> case rtw of
            TypeCheckerClassRefType crtw -> L crtw
            TypeCheckerTypeVariableRefType sn' -> T sn'
            TypeCheckerArrayRefType rtw -> U -}

getFieldTypeWithResolvedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> FieldDeclaration -> StateT ValidTypeClassData IO Type
getFieldTypeWithResolvedTypeParams vtqnw envMap fd = do
  maybeResolvedType <- getMappedFieldDeclaration'
    (\(FieldDeclaration f) -> do
      let t = getFieldType f
      resolveTypeParam t)
    vtqnw
    envMap
    fd
  case maybeResolvedType of
    Just resolvedType -> return resolvedType
    Nothing -> error ("Unable to resolve type params in field declaration: "++show vtqnw++" "++show fd)

getFieldTypeWithErasedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> FieldDeclaration -> StateT ValidTypeClassData IO Type
getFieldTypeWithErasedTypeParams vtqnw envMap fd = do
  maybeResolvedType <- getMappedFieldDeclaration'
    (\(FieldDeclaration f) -> do
      let t = getFieldType f
      eraseTypeParam (getFieldClassName f) t)
    vtqnw
    envMap
    fd
  case maybeResolvedType of
    Just resolvedType -> return resolvedType
    Nothing -> error ("Unable to resolve type params in field declaration: "++show vtqnw++" "++show fd)

getMappedFieldDeclaration' ::  (FieldDeclaration ->
                                  ReaderT TypeParamEnvironment (StateT ValidTypeClassData IO) Type) ->
                              TypeCheckerValidTypeQualifiedNameWrapper ->
                              TypeParamEnvironment ->
                              FieldDeclaration ->
                              StateT ValidTypeClassData IO (Maybe Type)
getMappedFieldDeclaration' mapper vtqnw envMap fieldDeclaration@(FieldDeclaration fd) = do
  if vtqnw == getFieldClassName fd
    then
      Just <$> runReaderT (mapper fieldDeclaration) envMap
    else do
      (TypeInfo clazz) <- getClassTypeInfo' vtqnw
      let (TypeCheckerClassReferenceTypeWrapper parentVtqnw maybeParentTypeArgs) = getTypeParent clazz
      (TypeInfo parentClazz) <- getClassTypeInfo' parentVtqnw
      if getTypeName clazz /= CP.createValidTypeNameObject || not (faStatic (getFieldAttributes fd))
        then do
          let parentEnv = case maybeParentTypeArgs of
                Nothing -> Map.empty
                Just parentTypeArgs ->
                  let substitutedParentTypeArgs = substituteTypeArgs parentTypeArgs envMap
                  in
                    buildTypeParamEnvironment (getTypeParameters parentClazz) substitutedParentTypeArgs
          getMappedFieldDeclaration' mapper parentVtqnw parentEnv fieldDeclaration
        else
          error ("Unable to resolve type params in field declaration: "++show vtqnw)

addNarrowingCast :: TypedTerm -> Type -> StateT ValidTypeClassData IO TypedTerm
addNarrowingCast typedTerm targetType = do
  let termType = getTypedTermType typedTerm
      erasedTermType = getTypedTermErasedType [] typedTerm
      erasedReturnType = getErasedType [] targetType
  (if isTypePrimitive termType || (erasedTermType == erasedReturnType)
    then
      return typedTerm
    else do
      return $ TypedCast (TypedReferenceTerm (TypeCheckerClassRefType (getTypeClassReferenceType termType)) typedTerm))
