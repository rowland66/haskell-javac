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
import Control.Monad (join,foldM,liftM,liftM2)
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

data TypedAbstraction = TypedFieldAccess {fName :: P.SimpleName, fTyp :: Type}
                      | TypedMethodInvocation { mName :: P.SimpleName
                                              , mTyp :: Type
                                              , mArgumentTyps :: [Type]
                                              , mArgumentTerms :: [TypedTerm]
                                              , mErasedType :: Type
                                              , mErasedArgumentTypes :: [Type]}
                      | TypedInterfaceMethodInvocation  { iName :: P.SimpleName
                                                        , iTyp :: Type
                                                        , iArgumentTyps :: [Type]
                                                        , iArgumentTerms :: [TypedTerm]
                                                        , iErasedType :: Type
                                                        , iErasedArgumentTypes :: [Type]}
                      | TypedSuperMethodInvocation  { smName :: P.SimpleName
                                                    , smTyp :: Type
                                                    , smParamTyps :: [Type]
                                                    , smTerms :: [TypedTerm]}
                      deriving Show

data TypedStaticAbstraction = TypedStaticFieldAccess {tfName :: P.SimpleName, tfTyp :: Type}
                      | TypedStaticMethodInvocation {tmName :: P.SimpleName, tmTyp :: Type, tmParamTyps :: [Type], tmTerms :: [TypedTerm]}
                      deriving Show

data TypedValue = TypedVariable {vPosition :: Word8, vTyp :: Type}
                | TypedIntegerLiteral {iValue :: Int32 }
                | TypedStringLiteral {sValue :: String }
                | TypedBooleanLiteral {bValue :: Bool }
                | TypedObjectCreation {ocTyp :: TypeCheckerClassReferenceTypeWrapper, ocParamTyps :: [Type], ocTerms :: [TypedTerm]}
                deriving Show

data TypedTerm = TypedValue TypedValue
               | TypedApplication TypedReferenceTerm TypedAbstraction
               | TypedStaticApplication TypedTypeName TypedStaticAbstraction
               | TypedCast TypedReferenceTerm
               | TypedConditional TypedTerm TypedTerm TypedTerm Type
               deriving Show

newtype TypedTypeName = TypedTypeName TypeCheckerValidTypeQualifiedNameWrapper deriving Show

data TypedReferenceTerm = TypedReferenceTerm TypeCheckerClassReferenceTypeWrapper TypedTerm deriving Show

data TypedConstructorInvocation = NewTypedConstructorInvocation TypeCheckerValidTypeQualifiedNameWrapper [Type] [TypedTerm] deriving Show

data TypedAssignment = NewTypedAssignment TypedTerm TypedTerm deriving Show

data TypedMethod = NewTypedMethod P.SimpleName [ValidTypeParameter] TypeCheckerClassReferenceTypeWrapper (Maybe TypedMethodImplementation)
                 deriving Show

data TypedClazz = NewTypedClazz [P.ClassAccessFlag] TypeCheckerValidTypeQualifiedNameWrapper TypeCheckerValidTypeQualifiedNameWrapper [ValidTypeField] [TypedMethod]
                deriving Show

data TypedMethodImplementation = TypedMethodImpl TypedTerm
                               | TypedConstructorImpl TypedConstructorInvocation [TypedAssignment]
                               deriving Show

init' = T.pack "<init>"

getValidTypeTermPosition :: ValidTypeTerm -> SourcePos
getValidTypeTermPosition (ValidTypeValue (ValidTypeVariable pos _)) = pos
getValidTypeTermPosition (ValidTypeValue (ValidTypeIntegerLit pos _)) = pos
getValidTypeTermPosition (ValidTypeValue (ValidTypeStringLit pos _)) = pos
getValidTypeTermPosition (ValidTypeValue (ValidTypeBooleanLit pos _)) = pos
getValidTypeTermPosition (ValidTypeValue (ValidTypeObjectCreation pos _ _)) = pos
getValidTypeTermPosition (ValidTypeCast (ValidTypeRefTypeDeclaration pos _) _) = pos
getValidTypeTermPosition (ValidTypeApplication (ValidTypeApplicationTargetTerm t) _) = getValidTypeTermPosition t
getValidTypeTermPosition (ValidTypeApplication (ValidTypeApplicationTargetTypeName (ValidTypeRefTypeDeclaration pos _)) _) = pos
getValidTypeTermPosition (ValidTypeConditional t _ _) = getValidTypeTermPosition t

getTypedTermType :: TypedTerm -> Type
getTypedTermType (TypedValue TypedVariable {vTyp=tp}) = tp
getTypedTermType (TypedValue TypedIntegerLiteral {}) = L CP.createValidTypeClassTypeInteger
getTypedTermType (TypedValue TypedStringLiteral {}) = L CP.createValidTypeClassTypeString
getTypedTermType (TypedValue TypedBooleanLiteral {}) = L CP.createValidTypeClassTypeBoolean
getTypedTermType (TypedValue TypedObjectCreation {ocTyp=crtw}) = L crtw
getTypedTermType (TypedApplication _ TypedFieldAccess {fTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedMethodInvocation {mTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedInterfaceMethodInvocation {iTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedSuperMethodInvocation {smTyp=tp}) = tp
getTypedTermType (TypedStaticApplication _ TypedStaticFieldAccess {tfTyp=tp}) = tp
getTypedTermType (TypedStaticApplication _ TypedStaticMethodInvocation {tmTyp=tp}) = tp
getTypedTermType (TypedCast (TypedReferenceTerm tp _)) = L tp
getTypedTermType (TypedConditional _ _ _ t) = t

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
      (maybeTypeErrors,(classPath',_)) <- lift $ runStateT typeCheckValidTypes (classPath,validTypeMap)
      case maybeTypeErrors of
        Just typeErrors -> return $ Left typeErrors
        Nothing -> do
          (typedClazzsE, (classPath'',_)) <- lift $ runStateT transformToTyped (classPath',validTypeMap)
          put (classPath'',localClasses)
          case typedClazzsE of
            Left typeErrors -> return $ Left typeErrors
            Right typedClazzs -> return $ Right typedClazzs

typeCheckValidTypes :: StateT ValidTypeClassData IO (Maybe [TypeError])
typeCheckValidTypes = do
  lift $ print "checkForDuplicateTypeErrors"
  result1 <- checkForDuplicateTypeErrors
  lift $ print "checkForClassInheritenceCycles"
  result3 <- checkForClassInheritenceCycles
  lift $ print "checkForAbstractClassSubClassErrors"
  result4 <- checkForAbstractClassSubClassErrors
  lift $ print "checkForNonReturnTypeSubstitutableOverrides"
  result5 <- checkForNonReturnTypeSubstitutableOverrides
  lift $ print "checkForConstructorsUnassignedFieldErrors"
  result6 <- checkForConstructorsUnassignedFieldErrors
  return $ result1 AP.<|> result3 AP.<|> result4 AP.<|> result5 AP.<|> result6

transformToTyped :: StateT ValidTypeClassData IO (Either [TypeError] [TypedClazz])
transformToTyped = do
  typeData@(_,classMap) <- get
  clazzList <- foldM (\list cls -> (list ++) <$> fmap (: []) (V.toEither <$> getTypedClazz cls)) [] classMap
  --lift $ print ("clazzList: "++show clazzList)
  let (typeErrors, typedClazzs) = Either.partitionEithers clazzList
  if not (null typeErrors)
    then return $ Left (concat typeErrors)
    else return $ Right typedClazzs

checkForDuplicateTypeErrors :: StateT ValidTypeClassData IO (Maybe [TypeError])
checkForDuplicateTypeErrors = do
  typeData@(_,classMap) <- get
  let errors = foldr (\cls list -> getDuplicateFields cls ++ getDuplicateMethods cls ++ list) [] classMap
  return $ case errors of
    [] -> Nothing
    _ -> Just errors

checkForClassInheritenceCycles :: StateT ValidTypeClassData IO (Maybe [TypeError])
checkForClassInheritenceCycles = checkForErrors getClassInheritenceCycleErrors

checkForAbstractClassSubClassErrors :: StateT ValidTypeClassData IO (Maybe [TypeError])
checkForAbstractClassSubClassErrors = checkForErrors getAbstractClassSubClassErrors

checkForNonReturnTypeSubstitutableOverrides :: StateT ValidTypeClassData IO (Maybe [TypeError])
checkForNonReturnTypeSubstitutableOverrides = checkForErrors getNonReturnTypeSubstitutableOverrideErrors

checkForConstructorsUnassignedFieldErrors :: StateT ValidTypeClassData IO (Maybe [TypeError])
checkForConstructorsUnassignedFieldErrors = checkForErrors getConstructorsUnassignedFieldErrors

checkForErrors :: (ValidTypeClazz -> StateT ValidTypeClassData IO [TypeError]) -> StateT ValidTypeClassData IO (Maybe [TypeError])
checkForErrors getErrorsFunction = do
  typeData@(_,classMap) <- get
  errors <- foldM (\list cls -> (list ++) <$> getErrorsFunction cls) [] classMap
  return $ case errors of
    [] -> Nothing
    _ -> Just errors

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

getType (ValidTypeValue (ValidTypeObjectCreation pos tp@(TypeCheckerClassReferenceTypeWrapper _ maybeTypeArgs) params)) = do
  cond <- lift $ isConcreteClass tp
  if not cond
    then return $ V.Failure [TypeError ("Illegal creation of abstract type: "++show tp) pos]
    else do
      typeData <- lift get
      createClass <- lift $ getClassTypeInfo tp
      paramTermsV <- sequenceA <$> mapM getType params
      case paramTermsV of
        V.Failure typeErrors -> return $ V.Failure typeErrors
        V.Success paramTerms -> do
          let signature = MethodSignature init' (fmap getTypedTermType paramTerms)
          eitherMethodInvocationExists <- lift $ getMethodDeclaration tp signature
          case eitherMethodInvocationExists of
            Left errStr -> return $ V.Failure [TypeError errStr pos]
            Right (MethodDeclaration m) -> do
              let targetParamTypes = getMethodParams m
              return $ V.Success (TypedValue (TypedObjectCreation {ocTyp=tp, ocParamTyps=targetParamTypes,ocTerms=paramTerms}))

getType (ValidTypeCast (ValidTypeRefTypeDeclaration pos tp) t) = do
  typeData <- lift get
  typedTermV <- getType t
  case typedTermV of
    V.Failure tes -> return $ V.Failure tes
    V.Success typedTerm -> do
      let typedTermType = getTypedTermType typedTerm
      let termTypeInfo = getBoxedType (getTypedTermType typedTerm)
      let castTypeInfo = tp
      isSubtype <- lift $ isSubtypeOf (TypeCheckerClassRefType castTypeInfo) (TypeCheckerClassRefType termTypeInfo)
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
                  Just typeArgs -> buildTypeParamEnvironment (getTypeParameters termTi) (VT.toList typeArgs)
            tp <- lift $ getFieldTypeWithResolvedTypeParams typeName typeParamEnvironment fieldDeclaration
            if faStatic (getFieldAttributes f)
              then return $
                V.Success
                  (TypedStaticApplication
                    (TypedTypeName
                      (getErasedTypeName crtw))
                    (TypedStaticFieldAccess {tfName=nm,tfTyp=tp}))
              else return $
                V.Success
                  (TypedApplication
                    (TypedReferenceTerm crtw typedTerm)
                    (TypedFieldAccess {fName=nm,fTyp=tp}))
      T sn -> undefined
      _ -> return $ V.Failure [TypeError "term with primitive type cannot be dereferenced" pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTerm t) (ValidTypeMethodInvocation pos nm arguments)) = do
  typedTermV <- getType t
  argumentTermsV <- sequenceA <$> mapM getType arguments
  let termTupleV = (,) <$> typedTermV <*> argumentTermsV
  case termTupleV of
    V.Failure tes -> return $ V.Failure tes
    V.Success (typedTerm,argumentTerms) -> do
      let signature = MethodSignature (P.deconstructSimpleName nm) (fmap getTypedTermType argumentTerms)
      case getTypedTermType typedTerm of
        L crtw@(TypeCheckerClassReferenceTypeWrapper _ maybeTypeArguments) -> do
          eitherMethodType <- lift $ getMethodDeclaration crtw signature
          case eitherMethodType of
            Left errStr -> return $ V.Failure [TypeError errStr pos]
            Right methodDeclaration@(MethodDeclaration m) -> do
              if maStatic (getMethodAttributes m)
                then return $ V.Success
                  (TypedStaticApplication
                    (TypedTypeName (getErasedTypeName crtw))
                    (TypedStaticMethodInvocation {tmName=nm,tmTyp=getMethodType m,tmParamTyps=getMethodParams m,tmTerms=argumentTerms}))
                else do
                  (TypeInfo ti) <- lift $ getClassTypeInfo crtw
                  let paramaterizedTypeEnvMap = case maybeTypeArguments of
                        Nothing -> Map.empty
                        Just typeArgs -> buildTypeParamEnvironment (getTypeParameters ti) (VT.toList typeArgs)
                  returnType <- lift $ getMethodTypeWithResolvedTypeParams (getTypeName ti) paramaterizedTypeEnvMap methodDeclaration
                  argumentTypes <- lift $ getSignatureWithResolvedTypeParams (getTypeName ti) paramaterizedTypeEnvMap methodDeclaration
                  erasedReturnType <- lift $ getMethodTypeWithErasedTypeParams (getTypeName ti) paramaterizedTypeEnvMap methodDeclaration
                  erasedArgumentTypes <- lift $ getSignatureWithErasedTypeParams (getTypeName ti) paramaterizedTypeEnvMap methodDeclaration
                  let methodInvocation =
                        if caInterface (getTypeAccessFlags ti)
                          then
                            (TypedInterfaceMethodInvocation  { iName=nm
                              ,iTyp=returnType
                              ,iArgumentTyps=argumentTypes
                              ,iArgumentTerms=argumentTerms
                              ,iErasedType=erasedReturnType
                              ,iErasedArgumentTypes=erasedArgumentTypes})
                          else
                            (TypedMethodInvocation  { mName=nm
                              ,mTyp=returnType
                              ,mArgumentTyps=argumentTypes
                              ,mArgumentTerms=argumentTerms
                              ,mErasedType=erasedReturnType
                              ,mErasedArgumentTypes=erasedArgumentTypes})
                  let application = V.Success
                        (TypedApplication
                          (TypedReferenceTerm crtw typedTerm)
                          methodInvocation)
                  if returnType == erasedReturnType && not (isTypeParameterized returnType)
                    then
                      return application
                    else
                      return $ TypedCast <$> (TypedReferenceTerm (getTypeClassReferenceType returnType) <$> application)
        _ -> return $ V.Failure [TypeError "term with primitive type cannot be dereferenced" pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTerm t) (ValidTypeSuperMethodInvocation pos nm params)) = do
  typedTermV <- getType t
  paramTermsV <- sequenceA <$> mapM getType params
  let termTupleV = (,) <$> typedTermV <*> paramTermsV
  case termTupleV of
    V.Failure tes -> return $ V.Failure tes
    V.Success (typedTerm, paramTerms) -> do
      let signature = MethodSignature (P.deconstructSimpleName nm) (fmap getTypedTermType paramTerms)
      case getTypedTermType typedTerm of
        L termTypeName -> do
          (TypeInfo termType) <- lift $ getClassTypeInfo termTypeName
          let parent = getTypeParent termType
          eitherMethodType <- lift $ getMethodDeclaration parent signature
          case eitherMethodType of
            Left errStr -> return $ V.Failure [TypeError errStr pos]
            Right (MethodDeclaration m) -> if maStatic (getMethodAttributes m)
              then return $ V.Failure [TypeError ("Super method is abstract: "++show parent++":"++show signature) pos]
              else return $ V.Success
                (TypedApplication
                  (TypedReferenceTerm parent typedTerm)
                  (TypedSuperMethodInvocation {smName=nm,smTyp=getMethodType m,smParamTyps=getMethodParams m,smTerms=paramTerms}))
        _ -> return $ V.Failure [TypeError "term with primitive type cannot be dereferenced" pos]

getType (ValidTypeApplication
          (ValidTypeApplicationTargetTypeName
            tn@(ValidTypeRefTypeDeclaration tnPos vtn@(TypeCheckerClassReferenceTypeWrapper vtqnw _)))
        (ValidTypeFieldAccess pos nm)) = do
    typeNameTypeInfo <- lift $ getClassTypeInfo' vtqnw
    maybeFieldDeclaration <- lift $ getFieldDeclaration typeNameTypeInfo nm
    case maybeFieldDeclaration of
      Nothing -> return $ V.Failure [TypeError ("Undefined static field: "++show vtn++":"++show nm) pos]
      Just (FieldDeclaration f) ->
        if faStatic (getFieldAttributes f)
          then return $
            V.Success (TypedStaticApplication (TypedTypeName vtqnw) (TypedStaticFieldAccess {tfName=nm,tfTyp=getFieldType f}))
          else return $
            V.Failure [TypeError ("non-static field "++show (getFieldName f)++" cannot be referenced from a static context") pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTypeName tn@(ValidTypeRefTypeDeclaration tnPos crtw)) (ValidTypeMethodInvocation pos nm params)) = do
  paramTypedTermsV <- sequenceA <$> mapM getType params
  case paramTypedTermsV of
    V.Failure tes -> return $ V.Failure tes
    V.Success paramTypedTerms -> do
      let signature = MethodSignature (P.deconstructSimpleName nm) (fmap getTypedTermType paramTypedTerms)
      typeNameTypeInfo <- lift $ getClassTypeInfo crtw
      eitherMethodInvocation <- lift $ getMethodDeclaration crtw signature
      case eitherMethodInvocation of
        Left errStr -> return $ V.Failure [TypeError errStr pos]
        Right (MethodDeclaration m) -> if maStatic (getMethodAttributes m)
          then return $ V.Success
            (TypedStaticApplication
              (TypedTypeName (getErasedTypeName crtw)) (TypedStaticMethodInvocation {tmName=nm,
                                                                tmTyp=getMethodType m,
                                                                tmParamTyps=getMethodParams m,
                                                                tmTerms=paramTypedTerms}))
          else
            return $ V.Failure [TypeError ("non-static method "++show (getMethodSignature m)++" cannot be referenced from a static context") pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTypeName tn@(ValidTypeRefTypeDeclaration tnPos vtn)) (ValidTypeSuperMethodInvocation pos nm params)) = undefined

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
        ifM (isSubtypeOf
              (TypeCheckerClassRefType (getBoxedType (getTypedTermType typedTerm)))
              (TypeCheckerClassRefType vmType))
          (return $ V.Success (NewTypedMethod methodName (VT.toList vmParams) vmType (Just (TypedMethodImpl typedTerm))))
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
          (NewTypedMethod P.createNameInit (VT.toList vmParams) CP.createValidTypeClassTypeObject (Just (TypedConstructorImpl typedThisCI typedAssignments)))
    Right typedSuperCIV -> do
      let tupleV = (,) <$> typedSuperCIV <*> typedAssignmentsV
      case tupleV of
        V.Failure tes -> return $ V.Failure tes
        V.Success (typedSuperCI,typedAssignments) -> return $ V.Success
          (NewTypedMethod P.createNameInit (VT.toList vmParams) CP.createValidTypeClassTypeObject (Just (TypedConstructorImpl typedSuperCI typedAssignments)))

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
      classTI <- lift $ getClassTypeInfo' vcName
      parentClasses <- lift $ getOrderedParentTypes (fst vcParent)
      parentClassesTI <- lift $ mapM getClassTypeInfo parentClasses
      let reducedMethods = List.foldl' combineMethodDeclList [] (classTI:parentClassesTI)
      let abstractMethods = filter (\(MethodDeclaration m) -> maAbstract (getMethodAttributes m)) reducedMethods
      if null abstractMethods
        then return ()
        else throwE [TypeError "Class does not implement abstract methods" vcSourcePos]

combineMethodDeclList ::  [MethodDeclaration] -> TypeInfo -> [MethodDeclaration]
combineMethodDeclList list (TypeInfo tp) = do
  let tpList = getTypeMethods tp
  List.unionBy methodDeclEq list tpList

methodDeclEq :: MethodDeclaration -> MethodDeclaration ->  Bool
methodDeclEq (MethodDeclaration m1)
             (MethodDeclaration m2) =
  getMethodName m1 == getMethodName m2 && getMethodParams m1 == getMethodParams m2

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
  let reducedMethods = List.foldl' combineMethodDeclList [] parentClassesTI
  let nonConstructorMethods = filter (\ValidTypeMethod {..} -> fst vmName /= P.createNameInit) vcMethods
  errorList <- lift $ foldM (\errors m -> (errors++) <$> isMethodOverrideNotReturnTypeSubstitutable reducedMethods m) [] nonConstructorMethods
  case errorList of
    [] -> return ()
    list -> throwE list

isMethodOverrideNotReturnTypeSubstitutable :: [MethodDeclaration] -> ValidTypeMethod -> StateT ValidTypeClassData IO [TypeError]
isMethodOverrideNotReturnTypeSubstitutable superClassMethods method@ValidTypeMethod {..} = do
  let (methodName,pos) = vmName
  let sig = mapValidTypeMethodToSignature method
  let possibleOverrideList = filter (\(MethodDeclaration m) -> sig == getMethodSignature m) superClassMethods
  case possibleOverrideList of
    [] -> return []
    (MethodDeclaration m):_ -> do
      let tp = getMethodType m
      if not (isTypeSupported tp)
        then return [TypeError "Method override of unsupported primitive return type" pos]
        else ifM (isSubtypeOf (TypeCheckerClassRefType vmType) (TypeCheckerClassRefType (getBoxedType tp)))
          (return [])
          (return [TypeError "Method override with incompatible return type" pos])

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
        else return $ V.Failure [TypeError ("Illegal assignment"++show leftTermTypeV) (getValidTypeTermPosition vaRightHandTerm)]

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
      eitherThisConstructor <- lift $ getMethodDeclaration crtw signature
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
      eitherSuperConstructor <- lift $ getMethodDeclaration parentCrtw signature
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

{--
Resolve an appropriate method for a method invocation expression (MethodSignature).
Logic derived from JLS 15.12
-}
getMethodDeclaration :: TypeCheckerClassReferenceTypeWrapper -> MethodSignature -> StateT ValidTypeClassData IO (Either String MethodDeclaration)
getMethodDeclaration crtw signature@(MethodSignature nm _) = do
  mdList <- getApplicableMethods crtw signature
  case mdList of
    [] -> return $ Left ("no suitable method found for "++show signature)
    _ -> do
      result <- getMostSpecificMethod crtw mdList
      case result of
        Nothing -> return $ Left ("reference to "++show nm++" is ambiguous")
        Just md -> return $ Right md

{--
Given a list of class methods, select the method that is most specific. The list of methods will be the result of a selction
process in which potentially applicable methods for a given method invocation are selected. Logic derived form JLS 15.12.2.5
-}
getMostSpecificMethod :: TypeCheckerClassReferenceTypeWrapper -> [MethodDeclaration] -> StateT ValidTypeClassData IO (Maybe MethodDeclaration)
getMostSpecificMethod crtw@(TypeCheckerClassReferenceTypeWrapper vtqnw _) mdList = do
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
            Just typeArgs -> buildTypeParamEnvironment (getTypeParameters ti) (VT.toList typeArgs)
      ms <- MethodSignature (showt (getMethodName m')) <$> getSignatureWithResolvedTypeParams vtqnw paramaterizedTypeEnvMap md'
      isMethodApplicableByLooseInvocation vtqnw paramaterizedTypeEnvMap md ms

getApplicableMethods :: TypeCheckerClassReferenceTypeWrapper -> MethodSignature -> StateT ValidTypeClassData IO [MethodDeclaration]
getApplicableMethods crtw@(TypeCheckerClassReferenceTypeWrapper vtqnw maybeTypeArguments) signature = do
  tiw@(TypeInfo ti) <- getClassTypeInfo crtw
  let !z = trace("type args: "++show maybeTypeArguments) 1
  let typeParameters = getTypeParameters ti
  let paramaterizedTypeEnvMap = case maybeTypeArguments of
        Nothing -> Map.empty
        Just typeArgs -> buildTypeParamEnvironment typeParameters (VT.toList typeArgs)
  pams <- getPotentiallyApplicableMethods tiw signature
  filterM (\md -> isMethodApplicableByLooseInvocation vtqnw paramaterizedTypeEnvMap md signature) pams

isMethodApplicableByLooseInvocation :: TypeCheckerValidTypeQualifiedNameWrapper ->
                                       TypeParamEnvironment ->
                                       MethodDeclaration ->
                                       MethodSignature ->
                                       StateT ValidTypeClassData IO Bool
isMethodApplicableByLooseInvocation vtqnw paramaterizedTypeEnvMap md signature@(MethodSignature searchName searchParams) = do
    let !z = trace ("signature: "++show signature++"--"++show paramaterizedTypeEnvMap) 1
    substitutedParams <- getSignatureWithResolvedTypeParams vtqnw paramaterizedTypeEnvMap md
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
  let (SimpleName nmane, _) = vmName
      paramTypes = VT.toList vmParams
  in
    MethodSignature nmane (fmap mapParameterToType paramTypes)

mapParameterToType :: ValidTypeParameter -> Type
mapParameterToType ValidTypeParameter {..} = L vpType

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
  return $ reverse $ CP.createValidTypeClassTypeObject:listWithoutObject

buildTypeParamEnvironment :: [TypeCheckerTypeParameter] -> [TypeCheckerTypeArgument] -> TypeParamEnvironment
buildTypeParamEnvironment genericTypeParams typeArgs =
  Map.fromList (
    zip
      (fmap
        (\(TypeCheckerTypeParameter paramName _) -> paramName)
        genericTypeParams)
      (fmap
        (\(TypeCheckerTypeArgument _ rtw) -> rtw)
        typeArgs))

getDirectSupertypeSet :: TypeCheckerReferenceTypeWrapper -> StateT ValidTypeClassData IO (Set.Set TypeCheckerReferenceTypeWrapper)
getDirectSupertypeSet(TypeCheckerClassRefType refType) | CP.createValidTypeClassTypeObject == refType = return Set.empty
getDirectSupertypeSet(TypeCheckerClassRefType refType@(TypeCheckerClassReferenceTypeWrapper vtqnw maybeTypeArgs)) = do
  (TypeInfo ti) <- getClassTypeInfo' vtqnw
  let refTypeTypeParams = getTypeParameters ti
  let parentCrtw@(TypeCheckerClassReferenceTypeWrapper parentVtqnw maybeParentTypeArgs) = getTypeParent ti
  let typeParamEnv = case maybeTypeArgs of
        Nothing -> Map.empty
        Just typeArgs -> buildTypeParamEnvironment refTypeTypeParams (VT.toList typeArgs)
  let substitutedParentCrtw = case maybeParentTypeArgs of
        Nothing -> parentCrtw
        Just typeArgs ->
          TypeCheckerClassReferenceTypeWrapper
            parentVtqnw
            (Just (VT.fromList (substituteTypeArgs (VT.toList typeArgs) typeParamEnv)))
  let interfaceCrtw = getTypeImplements ti
  let substitutedInterfaceCrtw =
        fmap
          (\interfaceCrtw'@(TypeCheckerClassReferenceTypeWrapper interfaceVtqnw maybeInterfaceTypeArgs) ->
            case maybeInterfaceTypeArgs of
              Nothing -> interfaceCrtw'
              Just typeArgs ->
                TypeCheckerClassReferenceTypeWrapper
                  interfaceVtqnw
                  (Just (VT.fromList (substituteTypeArgs (VT.toList typeArgs) typeParamEnv))))
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
        anyM (\rtw -> containsReferenceType parentRtw rtw) =<<
        (Set.toList <$> sts)
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

substituteTypeArgs :: [TypeCheckerTypeArgument] -> TypeParamEnvironment -> [TypeCheckerTypeArgument]
substituteTypeArgs typeArgs env =
  fmap (\ta -> substituteTypeArgument ta env) typeArgs

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
  return $ case t of
    I -> I
    Z -> Z
    U -> U
    L crtw -> L crtw
    T sn -> case envMap Map.!? sn of
      Nothing -> error ("Undefined type variable: "++ show sn ++ " in " ++ show envMap)
      Just rtw -> case rtw of
        TypeCheckerClassRefType crtw -> L crtw
        TypeCheckerTypeVariableRefType sn' -> T sn'
        TypeCheckerArrayRefType rtw -> U

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

getSignatureWithResolvedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> MethodDeclaration -> StateT ValidTypeClassData IO [Type]
getSignatureWithResolvedTypeParams vtqnw env md = do
  maybeResolvedSig <- getMappedMethodDeclaration' resolveTypeParams vtqnw env md
  case maybeResolvedSig of
    Just resolvedSig -> return resolvedSig
    Nothing -> error ("Unable to resolve type params in method signature: "++show vtqnw)

getSignatureWithErasedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> MethodDeclaration -> StateT ValidTypeClassData IO [Type]
getSignatureWithErasedTypeParams vtqnw env md@(MethodDeclaration m) = do
  maybeResolvedSig <- getMappedMethodDeclaration' eraseTypeParams vtqnw env md
  case maybeResolvedSig of
    Just resolvedSig -> return resolvedSig
    Nothing -> error ("Unable to erase type params in method signature: "++show vtqnw)

getMethodTypeWithResolvedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> MethodDeclaration -> StateT ValidTypeClassData IO Type
getMethodTypeWithResolvedTypeParams vtqnw envMap md = do
  maybeResolvedType <- getMappedMethodDeclaration'
    (\md@(MethodDeclaration m) -> do
      let t = getMethodType m
      resolveTypeParam t)
    vtqnw
    envMap
    md
  case maybeResolvedType of
    Just resolvedType -> return resolvedType
    Nothing -> error ("Unable to resolve type params in method signature: "++show vtqnw++" "++show md)

getMethodTypeWithErasedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> MethodDeclaration -> StateT ValidTypeClassData IO Type
getMethodTypeWithErasedTypeParams vtqnw envMap md = do
  maybeResolvedType <- getMappedMethodDeclaration'
    (\md@(MethodDeclaration m) -> do
      let t = getMethodType m
      eraseTypeParam (getMethodClassName m) t)
    vtqnw
    envMap
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
                  let substitutedTypeArgs = substituteTypeArgs (VT.toList interfaceTypeArgs) envMap
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
                      let substitutedParentTypeArgs = substituteTypeArgs (VT.toList parentTypeArgs) envMap
                      in
                        buildTypeParamEnvironment (getTypeParameters parentClazz) substitutedParentTypeArgs
              getMappedMethodDeclaration' mapper parentVtqnw parentEnv methodDeclaration
            else
              return Nothing

getFieldTypeWithResolvedTypeParams :: TypeCheckerValidTypeQualifiedNameWrapper -> TypeParamEnvironment -> FieldDeclaration -> StateT ValidTypeClassData IO Type
getFieldTypeWithResolvedTypeParams vtqnw envMap fieldDeclaration@(FieldDeclaration fd) = do
  let fieldType = case getFieldType fd of
        I -> I
        Z -> Z
        U -> U
        L crtw -> L crtw
        T sn -> case envMap Map.!? sn of
          Nothing -> error ("Undefined type variable: "++ show sn ++ " in " ++ show envMap)
          Just rtw -> case rtw of
            TypeCheckerClassRefType crtw -> L crtw
            TypeCheckerTypeVariableRefType sn' -> T sn'
            TypeCheckerArrayRefType rtw -> U

  if vtqnw == getFieldClassName fd
    then
      return fieldType
    else do
      (TypeInfo clazz) <- getClassTypeInfo' vtqnw
      let (TypeCheckerClassReferenceTypeWrapper parentVtqnw maybeParentTypeArgs) = getTypeParent clazz
      (TypeInfo parentClazz) <- getClassTypeInfo' parentVtqnw
      if getTypeName clazz /= CP.createValidTypeNameObject
        then do
          let parentEnv = case maybeParentTypeArgs of
                Nothing -> Map.empty
                Just parentTypeArgs ->
                  let substitutedParentTypeArgs = substituteTypeArgs (VT.toList parentTypeArgs) envMap
                  in
                    buildTypeParamEnvironment (getTypeParameters parentClazz) substitutedParentTypeArgs
          getFieldTypeWithResolvedTypeParams parentVtqnw parentEnv fieldDeclaration
        else
          error ("Unable to resolve type params in field declaration: "++show vtqnw)