{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}

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
  , TypeName
  , TypedTypeName(..)
  ) where

import Control.Monad.Trans.State.Strict (StateT,get,put,evalStateT,runStateT)
import Control.Monad.Trans.Reader (ReaderT, runReaderT, ask)
import Control.Monad (join,foldM,liftM,liftM2)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except ( ExceptT, runExceptT, throwE )
import Control.Monad.Extra ( foldM, ifM, join, filterM )
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
import Text.Parsec ( SourcePos )
import TextShow
import Data.Word ( Word8 )
import qualified Parser as P
import Text.Parsec.Pos ( SourcePos )
import qualified ClassPath as CP
import ClassPath ( ClassPath )
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
                      | TypedMethodInvocation {mName :: P.SimpleName, mTyp :: Type, mParamTyps :: [Type], mTerms :: [TypedTerm]}
                      | TypedSuperMethodInvocation {smName :: P.SimpleName, smTyp :: Type, smParamTyps :: [Type], smTerms :: [TypedTerm]}
                      deriving Show

data TypedStaticAbstraction = TypedStaticFieldAccess {tfName :: P.SimpleName, tfTyp :: Type}
                      | TypedStaticMethodInvocation {tmName :: P.SimpleName, tmTyp :: Type, tmParamTyps :: [Type], tmTerms :: [TypedTerm]}
                      deriving Show

data TypedValue = TypedVariable {vPosition :: Word8, vTyp :: Type}
                | TypedIntegerLiteral {iValue :: Int32 }
                | TypedStringLiteral {sValue :: String }
                | TypedBooleanLiteral {bValue :: Bool }
                | TypedObjectCreation {ocTyp :: ValidTypeName, ocParamTyps :: [Type], ocTerms :: [TypedTerm]}
                deriving Show

data TypedTerm = TypedValue TypedValue
               | TypedApplication TypedReferenceTerm TypedAbstraction
               | TypedStaticApplication TypedTypeName TypedStaticAbstraction
               | TypedCast TypedReferenceTerm
               | TypedConditional TypedTerm TypedTerm TypedTerm Type
               deriving Show

newtype TypedTypeName = TypedTypeName ValidTypeName deriving Show

data TypedReferenceTerm = TypedReferenceTerm ValidTypeName TypedTerm deriving Show

data TypedConstructorInvocation = NewTypedConstructorInvocation ValidTypeName [Type] [TypedTerm] deriving Show

data TypedAssignment = NewTypedAssignment TypedTerm TypedTerm deriving Show

data TypedMethod = NewTypedMethod P.SimpleName [ValidTypeParameter] ValidTypeName (Maybe TypedMethodImplementation)
                 deriving Show

data TypedClazz = NewTypedClazz [P.ClassAccessFlag] ValidTypeName ValidTypeName [ValidTypeField] [TypedMethod]

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
getValidTypeTermPosition (ValidTypeCast (ValidTypeTypeName pos _) _) = pos
getValidTypeTermPosition (ValidTypeApplication (ValidTypeApplicationTargetTerm t) _) = getValidTypeTermPosition t
getValidTypeTermPosition (ValidTypeApplication (ValidTypeApplicationTargetTypeName (ValidTypeTypeName pos _)) _) = pos
getValidTypeTermPosition (ValidTypeConditional t _ _) = getValidTypeTermPosition t

getTypedTermType :: TypedTerm -> Type
getTypedTermType (TypedValue TypedVariable {vTyp=tp}) = tp
getTypedTermType (TypedValue TypedIntegerLiteral {}) = L TypeValidator.createValidTypeNameInteger
getTypedTermType (TypedValue TypedStringLiteral {}) = L TypeValidator.createValidTypeNameString
getTypedTermType (TypedValue TypedBooleanLiteral {}) = L TypeValidator.createValidTypeNameBoolean
getTypedTermType (TypedValue TypedObjectCreation {ocTyp=tp}) = L tp
getTypedTermType (TypedApplication _ TypedFieldAccess {fTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedMethodInvocation {mTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedSuperMethodInvocation {smTyp=tp}) = tp
getTypedTermType (TypedStaticApplication _ TypedStaticFieldAccess {tfTyp=tp}) = tp
getTypedTermType (TypedStaticApplication _ TypedStaticMethodInvocation {tmTyp=tp}) = tp
getTypedTermType (TypedCast (TypedReferenceTerm tp _)) = L tp
getTypedTermType (TypedConditional _ _ _ t) = t

typeCheck :: LocalClasses -> StateT ClassPath IO (Either [TypeError] [TypedClazz])
typeCheck classMap = do
  classPath <- get
  (typedClazzE,(classPath',_)) <- lift $ runStateT typeCheck' (classPath,classMap)
  put classPath'
  return typedClazzE

typeCheck' :: StateT ClassData IO (Either [TypeError] [TypedClazz])
typeCheck' = do
  validTypesE <- transformToValidTypes
  case validTypesE of
    Left typeErrors -> return $ Left typeErrors
    Right validTypes -> do
      (classPath,_) <- get
      let validTypeMap = List.foldl' (\classMap validTypeClass@ValidTypeClazz {..} ->
            Map.insert vcName validTypeClass classMap) Map.empty validTypes
      (maybeTypeErrors,(classPath',_)) <- lift $ runStateT typeCheckValidTypes (classPath,validTypeMap)
      case maybeTypeErrors of
        Just typeErrors -> return $ Left typeErrors
        Nothing -> do
          typedClazzsE <- lift $ evalStateT transformToTyped (classPath',validTypeMap)
          case typedClazzsE of
            Left typeErrors -> return $ Left typeErrors
            Right typedClazzs -> return $ Right typedClazzs

typeCheckValidTypes :: StateT ValidTypeClassData IO (Maybe [TypeError])
typeCheckValidTypes = do
  result1 <- checkForDuplicateTypeErrors
  result3 <- checkForClassInheritenceCycles
  result4 <- checkForAbstractClassSubClassErrors
  result5 <- checkForNonReturnTypeSubstitutableOverrides
  result6 <- checkForConstructorsUnassignedFieldErrors
  return $ result1 AP.<|> result3 AP.<|> result4 AP.<|> result5 AP.<|> result6

transformToTyped :: StateT ValidTypeClassData IO (Either [TypeError] [TypedClazz])
transformToTyped = do
  typeData@(_,classMap) <- get
  clazzList <- foldM (\list cls -> (list ++) <$> fmap (: []) (V.toEither <$> getTypedClazz cls)) [] classMap
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

getType (ValidTypeValue (ValidTypeObjectCreation pos tp params)) = do
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
          eitherMethodInvocationExists <- lift $ getMethodDeclaration createClass signature
          case eitherMethodInvocationExists of
            Left errStr -> return $ V.Failure [TypeError errStr pos]
            Right (MethodDeclaration m) -> do
              let targetParamTypes = getMethodParams m
              return $ V.Success (TypedValue (TypedObjectCreation {ocTyp=tp, ocParamTyps=targetParamTypes,ocTerms=paramTerms}))

getType (ValidTypeCast (ValidTypeTypeName pos tp) t) = do
  typeData <- lift get
  typedTermV <- getType t
  case typedTermV of
    V.Failure tes -> return $ V.Failure tes
    V.Success typedTerm -> do
      let typedTermType = getTypedTermType typedTerm
      termTypeInfo <- lift $ getClassTypeInfo (getBoxedType (getTypedTermType typedTerm))
      castTypeInfo <- lift $ getClassTypeInfo tp
      isSubtype <- lift $ isSubtypeOf castTypeInfo termTypeInfo
      if isSubtype
        then return $ V.Success (TypedCast (TypedReferenceTerm tp typedTerm))
        else return $ V.Failure [TypeError ("Invalid cast: "++show tp) pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTerm t) (ValidTypeFieldAccess pos nm)) = do
  typedTermV <- getType t
  case typedTermV of
    V.Failure tes -> return $ V.Failure tes
    V.Success typedTerm -> case getTypedTermType typedTerm of
      L termTypeName -> do
        termType <- lift $ getClassTypeInfo termTypeName
        maybeFieldDeclaration <- lift $ getFieldDeclaration termType nm
        case maybeFieldDeclaration of
          Nothing -> return $ V.Failure [TypeError ("Undefined field: "++show nm) pos]
          Just (FieldDeclaration f) -> do
            let tp = getFieldType f
            if faStatic (getFieldAttributes f)
              then return $ V.Success (TypedStaticApplication (TypedTypeName termTypeName) (TypedStaticFieldAccess {tfName=nm,tfTyp=tp}))
              else return $ V.Success (TypedApplication (TypedReferenceTerm termTypeName typedTerm) (TypedFieldAccess {fName=nm,fTyp=tp}))
      _ -> return $ V.Failure [TypeError "term with primitive type cannot be dereferenced" pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTerm t) (ValidTypeMethodInvocation pos nm params)) = do
  typedTermV <- getType t
  paramTermsV <- sequenceA <$> mapM getType params
  let termTupleV = (,) <$> typedTermV <*> paramTermsV
  case termTupleV of
    V.Failure tes -> return $ V.Failure tes
    V.Success (typedTerm,paramTerms) -> do
      let signature = MethodSignature (P.deconstructSimpleName nm) (fmap getTypedTermType paramTerms)
      case getTypedTermType typedTerm of
        L termTypeName -> do
          termType <- lift $ getClassTypeInfo termTypeName
          eitherMethodType <- lift $ getMethodDeclaration termType signature
          case eitherMethodType of
            Left errStr -> return $ V.Failure [TypeError errStr pos]
            Right (MethodDeclaration m) ->
              if maStatic (getMethodAttributes m)
              then return $ V.Success
                (TypedStaticApplication
                  (TypedTypeName termTypeName)
                  (TypedStaticMethodInvocation {tmName=nm,tmTyp=getMethodType m,tmParamTyps=getMethodParams m,tmTerms=paramTerms}))
              else return $ V.Success
                (TypedApplication
                  (TypedReferenceTerm termTypeName typedTerm)
                  (TypedMethodInvocation {mName=nm,mTyp=getMethodType m,mParamTyps=getMethodParams m,mTerms=paramTerms}))
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
          termParentType <- lift $ getClassTypeInfo parent
          eitherMethodType <- lift $ getMethodDeclaration termParentType signature
          case eitherMethodType of
            Left errStr -> return $ V.Failure [TypeError errStr pos]
            Right (MethodDeclaration m) -> if maStatic (getMethodAttributes m)
              then return $ V.Failure [TypeError ("Super method is abstract: "++show parent++":"++show signature) pos]
              else return $ V.Success
                (TypedApplication
                  (TypedReferenceTerm parent typedTerm)
                  (TypedSuperMethodInvocation {smName=nm,smTyp=getMethodType m,smParamTyps=getMethodParams m,smTerms=paramTerms}))
        _ -> return $ V.Failure [TypeError "term with primitive type cannot be dereferenced" pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTypeName tn@(ValidTypeTypeName tnPos vtn)) (ValidTypeFieldAccess pos nm)) = do
    typeNameTypeInfo <- lift $ getClassTypeInfo vtn
    maybeFieldDeclaration <- lift $ getFieldDeclaration typeNameTypeInfo nm
    case maybeFieldDeclaration of
      Nothing -> return $ V.Failure [TypeError ("Undefined static field: "++show vtn++":"++show nm) pos]
      Just (FieldDeclaration f) ->
        if faStatic (getFieldAttributes f)
          then return $ V.Success (TypedStaticApplication (TypedTypeName vtn) (TypedStaticFieldAccess {tfName=nm,tfTyp=getFieldType f}))
          else return $ V.Failure [TypeError ("non-static field "++show (getFieldName f)++" cannot be referenced from a static context") pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTypeName tn@(ValidTypeTypeName tnPos vtn)) (ValidTypeMethodInvocation pos nm params)) = do
  paramTypedTermsV <- sequenceA <$> mapM getType params
  case paramTypedTermsV of
    V.Failure tes -> return $ V.Failure tes
    V.Success paramTypedTerms -> do
      let signature = MethodSignature (P.deconstructSimpleName nm) (fmap getTypedTermType paramTypedTerms)
      typeNameTypeInfo <- lift $ getClassTypeInfo vtn
      eitherMethodInvocation <- lift $ getMethodDeclaration typeNameTypeInfo signature
      case eitherMethodInvocation of
        Left errStr -> return $ V.Failure [TypeError errStr pos]
        Right (MethodDeclaration m) -> if maStatic (getMethodAttributes m)
          then return $ V.Success
            (TypedStaticApplication
              (TypedTypeName vtn) (TypedStaticMethodInvocation {tmName=nm,
                                                                tmTyp=getMethodType m,
                                                                tmParamTyps=getMethodParams m,
                                                                tmTerms=paramTypedTerms}))
          else
            return $ V.Failure [TypeError ("non-static method "++show (getMethodSignature m)++" cannot be referenced from a static context") pos]

getType (ValidTypeApplication (ValidTypeApplicationTargetTypeName tn@(ValidTypeTypeName tnPos vtn)) (ValidTypeSuperMethodInvocation pos nm params)) = undefined

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
            (tp@(L qn1),L qn2) | qn1 == qn2 -> return $ V.Success (TypedConditional booleanExpr term1 term2 tp)
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
  snd $ foldr (\method@ValidTypeMethod {..} (methodMap, duplicateList) ->
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

getClassInheritenceCycleErrors' :: ValidTypeClazz -> [ValidTypeName] -> StateT ValidTypeClassData IO [TypeError]
getClassInheritenceCycleErrors' ValidTypeClazz {..} classes = do
  (_,classMap) <- get
  let (parent,pos) = vcParent in
    if parent `elem` classes
      then return [TypeError ("Cyclic Inheritence: "++show vcName) pos]
      else if Map.member parent classMap
        then getClassInheritenceCycleErrors' (classMap Map.! parent) (parent : classes)
        else return []

getTypedClazz :: ValidTypeClazz -> StateT ValidTypeClassData IO (V.Validation [TypeError] TypedClazz)
getTypedClazz cls@ValidTypeClazz {..} = do
  typedMethodList <- getMethodsTermTypeErrors cls
  let (parentClass,_) = vcParent
  return $ NewTypedClazz (P.CPublic:vcAccessFlags) vcName parentClass vcFields <$> typedMethodList

getMethodsTermTypeErrors :: ValidTypeClazz -> StateT ValidTypeClassData IO (V.Validation [TypeError] [TypedMethod])
getMethodsTermTypeErrors cls@ValidTypeClazz {..} =
  foldM (\l m -> do
    typedMethodV <- getMethodTermTypeErrors cls m
    return $ (:) <$> typedMethodV <*> l)
  (V.Success [])
  vcMethods

getMethodTermTypeErrors :: ValidTypeClazz -> ValidTypeMethod -> StateT ValidTypeClassData IO (V.Validation [TypeError] TypedMethod)
getMethodTermTypeErrors cls@ValidTypeClazz {..} method@ValidTypeMethod {vmMaybeImpl=Nothing,..} = do
    let (methodName, _) = vmName
    return $ V.Success $ NewTypedMethod methodName vmParams vmType Nothing
getMethodTermTypeErrors cls@ValidTypeClazz {..} method@ValidTypeMethod {vmMaybeImpl=Just ValidTypeMethodImplementation{..},..} = do
    typeData <- get
    let (methodName, pos) = vmName
    let methodEnvironment = createMethodEnvironment typeData cls method
    typedTermV <- runReaderT (getType vmiTerm) methodEnvironment
    case typedTermV of
      V.Failure tes -> return $ V.Failure tes
      V.Success typedTerm -> do
        ifM (isSubtypeOf' (getBoxedType (getTypedTermType typedTerm)) vmType)
          (return $ V.Success (NewTypedMethod methodName vmParams vmType (Just (TypedMethodImpl typedTerm))))
          (return $ V.Failure [TypeError ("Incorrect return type: "++show (getTypedTermType typedTerm)) pos])
getMethodTermTypeErrors cls@ValidTypeClazz {..} method@ValidTypeMethod {vmMaybeImpl=Just ValidTypeConstructorImplementation{..},..} = do
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
          (NewTypedMethod P.createNameInit vmParams TypeValidator.createValidTypeNameObject (Just (TypedConstructorImpl typedThisCI typedAssignments)))
    Right typedSuperCIV -> do
      let tupleV = (,) <$> typedSuperCIV <*> typedAssignmentsV
      case tupleV of
        V.Failure tes -> return $ V.Failure tes
        V.Success (typedSuperCI,typedAssignments) -> return $ V.Success
          (NewTypedMethod P.createNameInit vmParams TypeValidator.createValidTypeNameObject (Just (TypedConstructorImpl typedSuperCI typedAssignments)))

defaultConstructorInvocation :: ValidTypeName -> TypedConstructorInvocation
defaultConstructorInvocation parentCls = NewTypedConstructorInvocation parentCls [] []

getAbstractClassSubClassErrors :: ValidTypeClazz -> StateT ValidTypeClassData IO [TypeError]
getAbstractClassSubClassErrors cls = do
  either <- runExceptT $ getAbstractClassSubClassErrors' cls
  case either of
    Left errors -> return errors
    Right _ -> return []

getAbstractClassSubClassErrors' :: ValidTypeClazz -> ExceptT [TypeError] (StateT ValidTypeClassData IO) ()
getAbstractClassSubClassErrors' cls@ValidTypeClazz {..} = do
  if P.CAbstract `elem` vcAccessFlags then return () else do
    parentClasses <- lift $ getSupertypeSet vcName
    parentClassesTI <- lift $ mapM getClassTypeInfo parentClasses
    reducedMethods <- lift $ foldM combineMethodDeclList [] (reverse parentClassesTI)
    let abstractMethods = filter (\(MethodDeclaration m) -> maAbstract (getMethodAttributes m)) reducedMethods
    if null abstractMethods
      then return ()
      else throwE [TypeError "Class does not implement abstract methods" vcSourcePos]

combineMethodDeclList ::  [MethodDeclaration] -> TypeInfo -> StateT ValidTypeClassData IO [MethodDeclaration]
combineMethodDeclList list (TypeInfo tp) = do
  let tpList = getTypeMethods tp
  unionByM methodDeclEq list tpList

methodDeclEq :: MethodDeclaration -> MethodDeclaration -> StateT ValidTypeClassData IO Bool
methodDeclEq (MethodDeclaration m1)
             (MethodDeclaration m2) =
  return $ getMethodName m1 == getMethodName m2 && getMethodParams m1 == getMethodParams m2

getNonReturnTypeSubstitutableOverrideErrors :: ValidTypeClazz -> StateT ValidTypeClassData IO [TypeError]
getNonReturnTypeSubstitutableOverrideErrors cls = do
  either <- runExceptT $ getNonReturnTypeSubstitutableOverrideErrors' cls
  case either of
    Left errors -> return errors
    Right _ -> return []

getNonReturnTypeSubstitutableOverrideErrors' :: ValidTypeClazz -> ExceptT [TypeError] (StateT ValidTypeClassData IO) ()
getNonReturnTypeSubstitutableOverrideErrors' cls@ValidTypeClazz {..} = do
  parentClasses <- lift $ getSupertypeSet (fst vcParent)
  parentClassesTI <- lift $ mapM getClassTypeInfo parentClasses
  reducedMethods <- lift $ foldM combineMethodDeclList [] (reverse parentClassesTI)
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
        else ifM (isSubtypeOf' vmType (getBoxedType tp))
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
      (TypeInfo rti) <- getClassTypeInfo (getBoxedType (getTypedTermType rightTermType))
      (TypeInfo lti) <- getClassTypeInfo (getBoxedType (getTypedTermType leftTermType))
      isSubtype <- isSubtypeOf' (getTypeName rti) (getTypeName lti)
      if isTermValidForLeftAssignment vaLeftHandTerm && isSubtype
        then return $ V.Success (NewTypedAssignment leftTermType rightTermType)
        else return $ V.Failure [TypeError "Illegal assignment" (getValidTypeTermPosition vaRightHandTerm)]

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
      typeInfo <- lift $ getClassTypeInfo vcName
      eitherThisConstructor <- lift $ getMethodDeclaration typeInfo signature
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
      let (parentClass, _) = vcParent
      let signature = MethodSignature init' (fmap getTypedTermType typedTerms)
      parentTypeInfo <- lift $ getClassTypeInfo parentClass
      eitherSuperConstructor <- lift $ getMethodDeclaration parentTypeInfo signature
      case eitherSuperConstructor of
        Left errStr -> return $ V.Failure [TypeError ("No invocation compatible constructor: "++show vcName++"."++show signature) pos]
        Right (MethodDeclaration m) ->
          return $ V.Success (NewTypedConstructorInvocation parentClass (getMethodParams m) typedTerms)

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
      unassignedFieldSet = Set.difference fieldSet assignedFieldSet
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

leastUpperBound :: [ValidTypeName] -> StateT ValidTypeClassData IO Type
leastUpperBound typeList = do
  st <- mapM getSupertypeSet typeList
  let ec = List.nub (List.foldl' List.intersect [] st)
  maybeLub <-foldM (\mec tp -> case mec of
                            Nothing -> return $ Just tp
                            Just tp' -> ifM (isSubtypeOf' tp tp') (return (Just tp)) (return (Just tp')))
    Nothing
    ec
  case maybeLub of
    Nothing -> return $ L TypeValidator.createValidTypeNameObject
    Just lub -> return $ L lub

getFieldDeclaration :: TypeInfo -> P.SimpleName -> StateT ValidTypeClassData IO (Maybe FieldDeclaration)
getFieldDeclaration ti@(TypeInfo t) nm = do
  let maybeFd = getTypeFieldDeclaration t nm
  case maybeFd of
    Just fd -> return $ Just fd
    Nothing ->
      if getTypeName t == TypeValidator.createValidTypeNameObject
        then return Nothing
        else do
          parentType <- getClassTypeInfo (getTypeParent t)
          getFieldDeclaration parentType nm

getMethodDeclaration :: TypeInfo -> MethodSignature -> StateT ValidTypeClassData IO (Either String MethodDeclaration)
getMethodDeclaration ti signature@(MethodSignature nm _) = do
  mdList <- getApplicableMethods ti signature
  case mdList of
    [] -> return $ Left ("no suitable method found for "++show signature)
    _ -> do
      result <- getMostSpecificMethod mdList
      case result of
        Nothing -> return $ Left ("reference to "++show nm++" is ambiguous")
        Just md -> return $ Right md

getMostSpecificMethod :: [MethodDeclaration] -> StateT ValidTypeClassData IO (Maybe MethodDeclaration)
getMostSpecificMethod mdList = do
  foldM foldFunc Nothing mdList
  where
    foldFunc result md =
      case result of
        r@(Just _) -> return r
        Nothing -> do
          ifM (isMostSpecific md) (return (Just md)) (return Nothing)
    isMostSpecific (MethodDeclaration m) =
      and <$> mapM (\candidate -> ifM (isMethodApplicableByLooseInvocation candidate (getMethodSignature m)) (return True) (return False)) mdList

getApplicableMethods :: TypeInfo -> MethodSignature -> StateT ValidTypeClassData IO [MethodDeclaration]
getApplicableMethods ti signature = do
  pams <- getPotentiallyApplicableMethods ti signature
  filterM (`isMethodApplicableByLooseInvocation` signature) pams

isMethodApplicableByLooseInvocation :: MethodDeclaration -> MethodSignature -> StateT ValidTypeClassData IO Bool
isMethodApplicableByLooseInvocation (MethodDeclaration m) signature@(MethodSignature searchName searchParams) = do
    areParametersInvocationCompatible (fmap (L . getBoxedType) searchParams)  (getMethodParams m)
  where
    areParametersInvocationCompatible :: [Type] -> [Type] -> StateT ValidTypeClassData IO Bool
    areParametersInvocationCompatible sigParamTypes candidateParams =
      foldM (\r (ptp, candidatetp) ->
        (r &&) <$> isTypeInvocationCompatible ptp candidatetp) True (zip sigParamTypes candidateParams)
    isTypeInvocationCompatible :: Type -> Type -> StateT ValidTypeClassData IO Bool
    isTypeInvocationCompatible (L baseType) I = isSubtypeOf' baseType TypeValidator.createValidTypeNameInteger
    isTypeInvocationCompatible (L baseType) Z = isSubtypeOf' baseType TypeValidator.createValidTypeNameBoolean
    isTypeInvocationCompatible (L baseType) (L vtn) = isSubtypeOf' baseType vtn
    isTypeInvocationCompatible _ _ = return False

getPotentiallyApplicableMethods :: TypeInfo -> MethodSignature -> StateT ValidTypeClassData IO [MethodDeclaration]
getPotentiallyApplicableMethods = getPotentiallyApplicableMethods' []

getPotentiallyApplicableMethods' :: [MethodDeclaration] -> TypeInfo -> MethodSignature -> StateT ValidTypeClassData IO [MethodDeclaration]
getPotentiallyApplicableMethods' mdList (TypeInfo t) sig = do
  mdList' <- getTypePotentiallyApplicableMethods t sig
  let mdList'' = List.foldl' (\l md@(MethodDeclaration md'') ->
        if any (\(MethodDeclaration md') -> isSubSignature (getMethodSignature md') (getMethodSignature md'')) l
          then l
          else md:l) mdList mdList'
  if getTypeName t == TypeValidator.createValidTypeNameObject
    then return mdList''
    else do
      parentType <- getClassTypeInfo (getTypeParent t)
      getPotentiallyApplicableMethods' mdList'' parentType sig

object = T.pack "java/lang/Object"
rparens = T.pack ")"
semi = T.pack ";"

mapValidTypeMethodToSignature :: ValidTypeMethod -> MethodSignature
mapValidTypeMethodToSignature method@ValidTypeMethod {..} =
  let (SimpleName nmane, _) = vmName
      paramTypes = vmParams
  in
    MethodSignature nmane (fmap (\ValidTypeParameter {..} -> L vpType) paramTypes)

mapParameterToType :: ValidTypeParameter -> Type
mapParameterToType ValidTypeParameter {..} = L vpType

{-- The signature of a method m1 is a subsignature of the signature of a method m2 if either:
     - m2 has the same signature as m1, or
     - the signature of m1 is the same as the erasure (§4.6) of the signature of m2.
-}
isSubSignature :: MethodSignature -> MethodSignature -> Bool
isSubSignature m1 m2 = m1 == m2

isConcreteClass :: ValidTypeName -> StateT ValidTypeClassData IO Bool
isConcreteClass tp = do
  (TypeInfo typeInfo) <- getClassTypeInfo tp
  return $ not (caAbstract (getTypeAccessFlags typeInfo))

isInterface :: ValidTypeName -> StateT ValidTypeClassData IO Bool
isInterface tp = do
  (TypeInfo typeInfo) <- getClassTypeInfo tp
  return $ caInterface (getTypeAccessFlags typeInfo)

isTypeBoolean :: Type -> Bool
isTypeBoolean Z = True
isTypeBoolean _ = False

isTypeInteger :: Type -> Bool
isTypeInteger I = True
isTypeInteger _ = False

getBoxedType :: Type -> ValidTypeName
getBoxedType I = TypeValidator.createValidTypeNameInteger
getBoxedType Z = TypeValidator.createValidTypeNameBoolean
getBoxedType tp@(L vtn) = vtn
getBoxedType _ = undefined

getUnboxedType :: Type -> Type
getUnboxedType (L vtn) | vtn == TypeValidator.createValidTypeNameBoolean = Z
                       | vtn == TypeValidator.createValidTypeNameInteger = I
getUnboxedType t = t

getSupertypeSet :: ValidTypeName -> StateT ValidTypeClassData IO [ValidTypeName]
getSupertypeSet tp = unfoldrM (\case
    Just vtn -> fmap (\(TypeInfo ti) -> Just (vtn, if vtn == TypeValidator.createValidTypeNameObject
                                          then Nothing
                                          else Just (getTypeParent ti)))
                (getClassTypeInfo vtn);
    Nothing -> return Nothing
  )
  (Just tp)

isSubtypeOf' :: ValidTypeName -> ValidTypeName -> StateT ValidTypeClassData IO Bool
isSubtypeOf' childType parentType = do
  childTI <- getClassTypeInfo childType
  parentTI <- getClassTypeInfo parentType
  isSubtypeOf childTI parentTI