{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}

module TypeChecker
  ( typeCheck
  , TypeError
  , transform
  , TypedAbstraction(..)
  , TypedValue(..)
  , TypedTerm(..)
  , TypedConstructorInvocation(..)
  , TypedAssignment(..)
  , TypedConstructor(..)
  , TypedMethod(..)
  , TypedClazz(..)
  , getTypedTermType
  , P.deconstructQualifiedName
  ) where

import Control.Monad.Trans.Reader
import Control.Monad (join,foldM,liftM,liftM2)
import Control.Monad.Trans.Class (lift)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Either as Either
import qualified Data.Maybe as Maybe
import qualified Data.Text as T
import TextShow
import Data.Word
import Parser2
import qualified Parser as P
import Environment
import ClassPath (ClassPath)
import qualified TypeInfo as TI
import Text.ParserCombinators.Parsec (SourcePos)
import Debug.Trace
import qualified Data.Sequence.Internal.Sorting as P
import Data.Maybe (mapMaybe)

type ClassData = (ClassPath,LocalClasses)

data TypedAbstraction = TypedFieldAccess {fName :: P.SimpleName, fTyp :: P.QualifiedName}
                      | TypedMethodInvocation {mName :: P.SimpleName, mTyp :: P.QualifiedName, mTerms :: [TypedTerm]}
                      deriving Show

data TypedValue = TypedVariable {vPosition :: Word8, vTyp :: P.QualifiedName}
                | TypedObjectCreation {ocTyp :: P.QualifiedName,  ocTerms :: [TypedTerm]}
                | TypedCast {cTyp :: P.QualifiedName,  cTerm :: TypedTerm}
                deriving Show

data TypedTerm = TypedValue TypedValue | TypedApplication TypedTerm TypedAbstraction deriving Show

data TypedConstructorInvocation = NewTypedConstructorInvocation [TypedTerm] deriving Show

data TypedAssignment = NewTypedAssignment TypedTerm TypedTerm deriving Show

data TypedConstructor = NewTypedConstructor [Parameter] TypedConstructorInvocation [TypedAssignment]

data TypedMethod = NewTypedMethod P.SimpleName [Parameter] P.QualifiedName TypedTerm deriving Show

data TypedClazz = NewTypedClazz P.QualifiedName Extends [Field] [TypedConstructor] [TypedMethod]

data TypeError = TypeError String SourcePos

instance Show TypeError where
  show (TypeError str pos) = str ++ "\nat: " ++ show pos

getTypedTermType :: TypedTerm -> P.QualifiedName
getTypedTermType (TypedValue TypedVariable {vTyp=tp}) = tp
getTypedTermType (TypedValue TypedObjectCreation {ocTyp=tp}) = tp
getTypedTermType (TypedValue TypedCast {cTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedFieldAccess {fTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedMethodInvocation {mTyp=tp}) = tp

typeCheck :: ClassData -> IO (Maybe [TypeError])
typeCheck typeData = do
  r1 <- checkForDuplicateTypeErrors typeData
  r2 <- mapM checkForDeclaredTypeErrors r1
  r3 <- mapM checkForClassInheritenceCycles (join r2)
  r4 <- mapM checkForConstructorsUnassignedFieldErrors (join r3)
  case r4 of
    Left errorList -> return $ Just errorList
    Right _ -> return Nothing

transform :: ClassData -> IO (Either [TypeError] [TypedClazz])
transform typeData@(_,classMap) = do
  clazzList <- foldM (\list cls -> (list ++) <$> fmap (: []) (runReaderT (getTypedClazz cls) typeData)) [] classMap
  let (typeErrors, typedClazzs) = Either.partitionEithers clazzList
  if not (null typeErrors)
    then return $ Left (concat typeErrors)
    else return $ Right typedClazzs

checkForDuplicateTypeErrors :: ClassData -> IO (Either [TypeError] ClassData)
checkForDuplicateTypeErrors typeData@(_,classMap) = do
  let errors = foldr (\cls list -> getDuplicateFields cls ++ getDuplicateMethods cls ++ list) ([] :: [TypeError]) classMap
  return $ case errors of
    [] -> Right typeData
    _ -> Left errors

checkForDeclaredTypeErrors :: ClassData -> IO (Either [TypeError] ClassData)
checkForDeclaredTypeErrors typeData@(_,classMap) = do
  errors <- foldM (\list cls -> runReaderT (getClassDeclaredTypeErrors cls) typeData >>=
              (\l -> (l ++) <$> runReaderT (getConstructorsDeclaredTypeErrors cls) typeData) >>=
              (\l -> (l ++) <$> runReaderT (getFieldDeclaredTypeErrors cls) typeData) >>=
              (\l -> (l ++) <$> runReaderT (getMethodsDeclaredTypeErrors cls) typeData) ) [] classMap
  case errors of
    [] -> return (Right typeData)
    _ -> return (Left errors)

checkForClassInheritenceCycles :: ClassData -> IO (Either [TypeError] ClassData)
checkForClassInheritenceCycles typeData = checkForErrors typeData getClassInheritenceCycleErrors

checkForConstructorsUnassignedFieldErrors :: ClassData -> IO (Either [TypeError] ClassData)
checkForConstructorsUnassignedFieldErrors classMap = checkForErrors classMap getConstructorsUnassignedFieldErrors

checkForErrors :: ClassData -> (Clazz2 -> ReaderT ClassData IO [TypeError]) -> IO (Either [TypeError] ClassData)
checkForErrors typeData@(_,classMap) getErrorsFunction = do
  errors <- foldM (\list cls -> (list ++) <$> runReaderT (getErrorsFunction cls) typeData) [] classMap
  return $ case errors of
    [] -> Right typeData
    _ -> Left errors

getType :: Term -> ReaderT (Environment, ClassData) IO (Either [TypeError] TypedTerm)
getType (Value (Variable pos x)) = do
  (env, typeData) <- ask
  return $ case env !? x of Just (tp,ndx) -> Right (TypedValue (TypedVariable {vPosition=fromIntegral ndx :: Word8,vTyp=tp})); Nothing -> Left [TypeError ("Undefined variable: "++show x) pos]
getType (Value (ObjectCreation pos tp params)) = do
  (env, typeData) <- ask
  eitherCreateClass <- lift $ TI.getClassTypeInfo typeData tp
  case eitherCreateClass of
    Left _ -> return (Left [TypeError ("Undefined type: "++show tp) pos])
    Right createClass -> do
      eitherParamTypes <- mapM getType params
      if null (Either.lefts eitherParamTypes) then do
        let paramTerms = Either.rights eitherParamTypes
        let signature = Signature P.createNameInit (fmap getTypedTermType paramTerms)
        eitherConstructorExists <- lift $ TI.hasConstructorWithSignature typeData createClass signature
        case eitherConstructorExists of
          Left txt -> return (Left [TypeError ("Undefined type: "++T.unpack txt) pos])
          Right constructorExists ->
            if constructorExists then
              return (Right (TypedValue (TypedObjectCreation {ocTyp=tp, ocTerms=paramTerms})))
            else
              return (Left [TypeError ("Undefined constructor: "++show tp++"."++show signature) pos])
      else return $ Left (concat (Either.lefts eitherParamTypes))
getType (Value (Cast pos tp t)) = do
  (env, typeData) <- ask
  eitherTypedTerm <- getType t
  case eitherTypedTerm of
    Left _ -> return eitherTypedTerm
    Right typedTerm -> do
      eitherTermTypeInfo <- lift $ TI.getClassTypeInfo typeData (getTypedTermType typedTerm)
      eitherCastTypeInfo <- lift $ TI.getClassTypeInfo typeData tp
      isSubtype <- lift $TI.isSubtypeOf' typeData eitherCastTypeInfo eitherTermTypeInfo
      case isSubtype of
        Left txt -> return $ Left [TypeError ("Undefined type: "++T.unpack txt) pos]
        Right b -> if b
          then return $ Right (TypedValue (TypedCast {cTyp=tp, cTerm=typedTerm}))
          else return $ Left [TypeError ("Invalid cast: "++show tp) pos]
getType (Application t (FieldAccess pos nm)) = do
  (env, typeData) <- ask
  eitherTypedTerm <- getType t
  case eitherTypedTerm of
    Left _ -> return eitherTypedTerm
    Right typedTerm -> do
      eitherTermType <- lift $ TI.getClassTypeInfo typeData (getTypedTermType typedTerm)
      case eitherTermType of
        Left txt -> return $ Left [TypeError ("Undefined type: "++T.unpack txt) pos]
        Right termType -> do
          maybeFieldType <- getFieldType nm termType
          case maybeFieldType of
            Nothing -> return $ Left [TypeError ("Undefined field: "++show nm) pos]
            Just tp -> return $ Right (TypedApplication typedTerm (TypedFieldAccess {fName=nm,fTyp=tp}))
getType (Application t (MethodInvocation pos nm params)) = do
  (env, typeData) <- ask
  eitherTypedTerm <- getType t
  eitherParamTypes <- mapM getType params
  if null (Either.lefts eitherParamTypes) then do
    let paramTypedTerms = Either.rights eitherParamTypes
    let signature = Signature nm (fmap getTypedTermType paramTypedTerms)
    case eitherTypedTerm of
      Left _ -> return eitherTypedTerm
      Right typedTerm -> do
        eitherTermType <- lift $ TI.getClassTypeInfo typeData (getTypedTermType typedTerm)
        case eitherTermType of
          Left txt -> return $ Left [TypeError ("Undefined type: "++T.unpack txt) pos]
          Right termType -> do
            maybeMethodType <- getMethodType signature termType
            case maybeMethodType of
              Nothing -> return (Left [TypeError ("Undefined method: "++show signature) pos])
              Just tp -> return (Right (TypedApplication typedTerm (TypedMethodInvocation {mName=nm,mTyp=tp,mTerms=paramTypedTerms})))
  else return $ Left (concat (Either.lefts eitherParamTypes))

getFieldType :: P.SimpleName -> TI.TypeInfo -> ReaderT (Environment, ClassData) IO (Maybe P.QualifiedName)
getFieldType nm tp = do
  (_, typeData) <- ask
  let maybeFieldType = TI.getFieldType tp nm
  case maybeFieldType of
    Just _ -> return maybeFieldType
    Nothing ->
      let parentName = TI.getTypeParent tp
      in
        if parentName == P.createQNameObject
          then return Nothing
          else do
            eitherParentType <- lift $ TI.getClassTypeInfo typeData parentName
            case eitherParentType of
              Left txt -> undefined -- This should never happen
              Right parentType -> getFieldType nm parentType

getMethodType :: Signature -> TI.TypeInfo -> ReaderT (Environment, ClassData) IO (Maybe P.QualifiedName)
getMethodType signature tp = do
  (_, typeData) <- ask
  let maybeMethodType = TI.getMethodType tp signature
  case maybeMethodType of
    Just _ -> return maybeMethodType
    Nothing ->
      let parentName = TI.getTypeParent tp
      in
        if parentName == P.createQNameObject
          then return Nothing
          else do
            eitherParentType <- lift $ TI.getClassTypeInfo typeData parentName
            case eitherParentType of
              Left txt -> undefined -- This should never happen
              Right parentType -> getMethodType signature parentType

getDuplicateFields :: Clazz2 -> [TypeError]
getDuplicateFields (NewClazz2 _ _ _ _ fields _ _) =
  snd $ foldr (\field@(NewField pos tp _ nm) (fieldMap, duplicateList) ->
    (case Map.lookup nm fieldMap of
      Nothing -> (Map.insert nm nm fieldMap, duplicateList)
      Just _ -> (fieldMap, TypeError ("Duplicate field: "++show nm) pos:duplicateList)))
    (Map.empty, [])
    fields

getDuplicateMethods :: Clazz2 -> [TypeError]
getDuplicateMethods (NewClazz2 _ _ _ _ _ _ methods) =
  snd $ foldr (\method@(NewMethod pos _ _ _ sig@(Signature nm params) _) (methodMap, duplicateList) ->
    (case Map.lookup nm methodMap of
      Nothing -> (Map.insert nm [params] methodMap, duplicateList)
      Just paramsList -> if params `elem` paramsList
        then (methodMap, TypeError ("Duplicate method: "++show sig) pos:duplicateList)
        else (Map.update (\l -> Just (params:l)) nm methodMap, duplicateList)))
    (Map.empty, [])
    methods

getClassDeclaredTypeErrors :: Clazz2 -> ReaderT ClassData IO [TypeError]
getClassDeclaredTypeErrors (NewClazz2 _ _ _ ExtendsObject _ _ _) = return []
getClassDeclaredTypeErrors (NewClazz2 _ _ _ (NewExtends pos parent) _ _ _) = do
  typeData <- ask
  lift $ do
           cond <- TI.isValidClass typeData parent
           return $ [TypeError ("Undefined type: "++show parent) pos | not cond]

getFieldDeclaredTypeErrors :: Clazz2 -> ReaderT ClassData IO [TypeError]
getFieldDeclaredTypeErrors (NewClazz2 _ _ _ _ fields _ _) = do
  typeData <- ask
  lift $ foldM (\errorList field@(NewField pos tp _ _) ->
    do
      cond <- TI.isValidClass typeData tp
      return $ if cond then errorList else TypeError ("Undefined type: "++show tp) pos:errorList)
    []
    fields

getMethodsDeclaredTypeErrors :: Clazz2 -> ReaderT ClassData IO [TypeError]
getMethodsDeclaredTypeErrors (NewClazz2 _ _ _ _ _ _ methods) =
  foldM (\errorList method -> fmap (++ errorList) (getMethodDeclaredTypeErrors method)) [] methods

getMethodDeclaredTypeErrors :: Method -> ReaderT ClassData IO [TypeError]
getMethodDeclaredTypeErrors method = do
  returnDeclaredTypeErrors <- getMethodReturnDeclaredTypeErrors method
  paramDeclaredTypeErrors <- getMethodParamDeclaredTypeErrors method
  expressionDeclaredTypeErrors <- getMethodExpressionDeclaredTypeErrors method
  return $ returnDeclaredTypeErrors ++ paramDeclaredTypeErrors ++ expressionDeclaredTypeErrors

getMethodReturnDeclaredTypeErrors :: Method -> ReaderT ClassData IO [TypeError]
getMethodReturnDeclaredTypeErrors (NewMethod pos _ _ tp _ _) = do
  typeData <- ask
  lift $ do
           cond <- TI.isValidClass typeData tp
           return $ [TypeError ("Undefined type: "++show tp) pos | not cond]

getMethodParamDeclaredTypeErrors :: Method -> ReaderT ClassData IO [TypeError]
getMethodParamDeclaredTypeErrors (NewMethod _ _ params _ _ _) =
  getParamDeclaredTypeErrors params

getMethodExpressionDeclaredTypeErrors :: Method -> ReaderT ClassData IO [TypeError]
getMethodExpressionDeclaredTypeErrors (NewMethod _ _ _ _ _ term) =
  getTermDeclaredTypeErrors term

getConstructorsDeclaredTypeErrors :: Clazz2 -> ReaderT ClassData IO [TypeError]
getConstructorsDeclaredTypeErrors (NewClazz2 _ _ _ _ _ constructors _) =
  foldM (\errorList (NewConstructor _ _ _ _ assignments) -> fmap (++ errorList) (getAssignmentsDeclaredTypeErrors assignments)) [] constructors

getConstructorDeclaredTypeErrors :: Constructor -> ReaderT ClassData IO [TypeError]
getConstructorDeclaredTypeErrors (NewConstructor _ params _ _ assignments) = do
  paramDeclaredTypeErrors <- getParamDeclaredTypeErrors params
  assignmentDeclaredTypeErrors <- getAssignmentsDeclaredTypeErrors assignments
  return $ paramDeclaredTypeErrors ++ assignmentDeclaredTypeErrors

getParamDeclaredTypeErrors :: [Parameter] -> ReaderT ClassData IO [TypeError]
getParamDeclaredTypeErrors params = do
  typeData <- ask
  lift $ foldM (\errorList (NewParameter pos tp _) ->
    do
      cond <- TI.isValidClass typeData tp
      return $ if cond then errorList else TypeError ("Undefined type: "++show tp) pos:errorList)
    []
    params

getAssignmentsDeclaredTypeErrors :: [Assignment]-> ReaderT ClassData IO [TypeError]
getAssignmentsDeclaredTypeErrors = foldM (\errorList a -> fmap (++ errorList) (getAssignmentDeclaredTypeErrors a)) []

getAssignmentDeclaredTypeErrors :: Assignment -> ReaderT ClassData IO [TypeError]
getAssignmentDeclaredTypeErrors (NewAssignment pos t1 t2) = do
  t1errors <- getTermDeclaredTypeErrors t1
  t2errors <- getTermDeclaredTypeErrors t2
  return (t1errors ++ t2errors)

getTermDeclaredTypeErrors :: Term -> ReaderT ClassData IO [TypeError]
getTermDeclaredTypeErrors t = do
  typeData <- ask
  case t of
    (Value (Variable _ _)) -> return []
    (Value (ObjectCreation pos tp params)) -> liftM2 (++) paramErrors classError
      where
        classError = lift $ do cond <- TI.isValidClass typeData tp; return $ [TypeError ("Undefined type: "++show tp) pos | not cond]
        paramErrors = foldM (\errs t' -> fmap (++ errs) (getTermDeclaredTypeErrors t')) [] params
    (Value (Cast pos tp term)) -> liftM2 (++) termError classError
      where
        classError = lift $ do cond <- TI.isValidClass typeData tp; return $ [TypeError ("Undefined type: "++show tp) pos | not cond]
        termError = getTermDeclaredTypeErrors term
    (Application t' (FieldAccess _ _)) -> getTermDeclaredTypeErrors t'
    (Application t' (MethodInvocation pos nm params)) ->  liftM2 (++) paramErrors termErrors
      where
        termErrors = getTermDeclaredTypeErrors t'
        paramErrors = foldM (\errs t'' -> fmap (++ errs) (getTermDeclaredTypeErrors t'')) [] params

getClassInheritenceCycleErrors :: Clazz2 -> ReaderT ClassData IO [TypeError]
getClassInheritenceCycleErrors clazz = getClassInheritenceCycleErrors' clazz []

getClassInheritenceCycleErrors' :: Clazz2 -> [P.QualifiedName] -> ReaderT ClassData IO [TypeError]
getClassInheritenceCycleErrors' (NewClazz2 _ _ _ ExtendsObject _ _ _) _ = return []
getClassInheritenceCycleErrors' (NewClazz2 _ _ nm (NewExtends pos parent) _ _ _) classes = do
  (_,classMap) <- ask
  if parent `elem` classes
    then return [TypeError ("Cyclic Inheritence: "++show nm) pos]
    else if Map.member parent classMap
      then getClassInheritenceCycleErrors' (classMap Map.! parent) (parent : classes)
      else return []

getTypedClazz :: Clazz2 -> ReaderT ClassData IO (Either [TypeError] TypedClazz)
getTypedClazz cls@(NewClazz2 _ _ name extends fields _ _) = do
  eitherCorE <- getConstructorsTypeErrors cls
  eitherMorE <- getMethodsTermTypeErrors cls
  return $ case eitherCorE of
    Left constructorErrors -> case eitherMorE of
      Left methodErrors -> Left (constructorErrors ++ methodErrors);
      Right _ -> Left constructorErrors
    Right typedConstructors -> case eitherMorE of
      Left methodErrors -> Left methodErrors;
      Right typedMethods -> Right (NewTypedClazz name extends fields typedConstructors typedMethods)

getMethodsTermTypeErrors :: Clazz2 -> ReaderT ClassData IO (Either [TypeError] [TypedMethod])
getMethodsTermTypeErrors cls@(NewClazz2 _ _ nm _ _ _ methods) = do
  typeData <- ask
  eitherList <-  lift $ mapM (\m -> getMethodTermTypeErrors cls m typeData) methods
  let (errorList, typedMethodList) = Either.partitionEithers eitherList
  return $ if not (null errorList) then Left (concat errorList) else Right typedMethodList

getMethodTermTypeErrors :: Clazz2 -> Method -> ClassData -> IO (Either [TypeError] TypedMethod)
getMethodTermTypeErrors cls method@(NewMethod pos nm params tp _ t) typeData = do
  let methodEnvironment = createMethodEnvironment typeData cls method
  eitherTypedTerm <- runReaderT (getType t) (methodEnvironment, typeData)
  case eitherTypedTerm of
    Left e -> return $ Left e
    Right typedTerm -> if tp == getTypedTermType typedTerm
      then return $ Right (NewTypedMethod nm params tp typedTerm);
      else return $ Left [TypeError ("Incorrect return type: "++show (getTypedTermType typedTerm)) pos]

getConstructorsTypeErrors :: Clazz2 -> ReaderT ClassData IO (Either [TypeError] [TypedConstructor])
getConstructorsTypeErrors cls@(NewClazz2 _ _ nm _ _ constructors _) = do
  typeData <- ask
  eitherList <- lift $ mapM (\c -> getConstructorTypeErrors cls c typeData) constructors
  let (errorList,constructorList) = Either.partitionEithers eitherList
  return $ if not (null errorList) then Left (concat errorList) else Right constructorList

getConstructorTypeErrors :: Clazz2 -> Constructor -> ClassData -> IO (Either [TypeError] TypedConstructor)
getConstructorTypeErrors cls@(NewClazz2 _ _ clsNm _ _ _ _) constructor@(NewConstructor pos params _ maybeConstructorInvocation assignments) typeData = do
  let constructorRightEnvironment = createConstructorEnvironmentRight typeData cls constructor
  let constructorLeftEnvironment = createConstructorEnvironmentLeft typeData cls
  maybeEitherC <- case maybeConstructorInvocation of
    Just ci -> do
      eitherTypedCI <- getTypedConstructorInvocation constructorRightEnvironment cls ci typeData
      case eitherTypedCI of
        Left e -> return $ Just $ Left e
        Right typedCI -> return $ Just $ Right typedCI
    Nothing -> return Nothing
  eitherList <- mapM
    (\a
        -> getAssignmentTypeError
            constructorLeftEnvironment constructorRightEnvironment a typeData) assignments
  let (assignmentTypeErrors,typedAssignments) = Either.partitionEithers eitherList
  case maybeEitherC of
    Just eitherC ->
      case eitherC of
        Left le -> return $ Left (le ++ concat assignmentTypeErrors)
        Right ci -> if not (null assignmentTypeErrors)
          then return $ Left (concat assignmentTypeErrors)
          else return $ Right (NewTypedConstructor params ci typedAssignments)
    Nothing ->
      if not (null assignmentTypeErrors)
        then return $ Left (concat assignmentTypeErrors)
        else return $ Right (NewTypedConstructor params defaultConstructor typedAssignments)

defaultConstructor :: TypedConstructorInvocation
defaultConstructor = NewTypedConstructorInvocation []

getAssignmentTypeError :: Environment -> Environment -> Assignment -> ClassData -> IO (Either [TypeError] TypedAssignment)
getAssignmentTypeError lenv renv (NewAssignment pos leftTerm rightTerm) typeData = do
  leftTermType <- runReaderT (getType leftTerm) (lenv, typeData)
  rightTermType <- runReaderT (getType rightTerm) (renv, typeData)
  case leftTermType of
    Left le -> case rightTermType of
      Left re -> return $ Left (le++re)
      Right _ -> return $ Left le
    Right ltp ->
      case rightTermType of
        Left re -> return $ Left re
        Right rtp -> do
          eitherrti <- TI.getClassTypeInfo typeData (getTypedTermType rtp)
          eitherlti <- TI.getClassTypeInfo typeData (getTypedTermType ltp)
          eitherIsSubtype <- TI.isSubtypeOf' typeData eitherrti eitherlti
          case eitherIsSubtype of
            Left txt -> return $ Left [TypeError ("Undefined type: "++T.unpack txt) pos]
            Right isSubtype -> if isTermValidForLeftAssignment leftTerm && isSubtype
              then return $ Right (NewTypedAssignment ltp rtp)
              else return $ Left [TypeError "Illegal assignment" pos]

isTermValidForLeftAssignment :: Term -> Bool
isTermValidForLeftAssignment (Application (Value (Variable _ target)) (FieldAccess _ _)) = P.createNameThis == target
isTermValidForLeftAssignment (Application t (FieldAccess _ _)) = isTermValidForLeftAssignment t
isTermValidForLeftAssignment t = False

getTypedConstructorInvocation :: Environment -> Clazz2 -> ConstructorInvocation -> ClassData -> IO (Either [TypeError] TypedConstructorInvocation)
getTypedConstructorInvocation constructorSuperInvocationEnvironment cls@(NewClazz2 _ _ _ extends _ _ _) (NewConstructorInvocation pos terms) typeData = do
  eitherTermTypes <- mapM (\t -> runReaderT (getType t) (constructorSuperInvocationEnvironment,typeData)) terms
  if null (Either.lefts eitherTermTypes) then
    let termTypes = Either.rights eitherTermTypes
        signature = Signature P.createNameInit (fmap getTypedTermType termTypes) in
        case extends of
          (NewExtends _ parentClass) -> do
            eitherParentTypeInfo <- TI.getClassTypeInfo typeData parentClass
            eitherCond <- TI.hasConstructorWithSignature' typeData eitherParentTypeInfo signature
            case eitherCond of
              Left txt -> return $ Left [TypeError ("Undefined type: "++T.unpack txt) pos]
              Right cond -> if cond
                then return $ Right (NewTypedConstructorInvocation termTypes)
                else return $ Left [TypeError ("No constructor in "++show parentClass++" with signature "++show signature) pos]
          ExtendsObject -> return $ Right (NewTypedConstructorInvocation termTypes)
  else return $ Left (concat (Either.lefts eitherTermTypes))

getConstructorsUnassignedFieldErrors :: Clazz2 -> ReaderT ClassData IO [TypeError]
getConstructorsUnassignedFieldErrors cls@(NewClazz2 _ _ nm _ _ constructors _) = do
  return $ foldr (\c list -> getConstructorUnassignedFieldError cls c ++ list) [] constructors

getConstructorUnassignedFieldError :: Clazz2 -> Constructor -> [TypeError]
getConstructorUnassignedFieldError cls@(NewClazz2 _ _ clsNm _ fields _ _) constructor@(NewConstructor pos _ signature _ assignments) =
  let fieldSet = Set.fromList (fmap (\(NewField _ _ _ nm) -> nm) fields)
      assignedFieldSet = Set.fromList (mapMaybe (\(NewAssignment _ term _) -> getAssignmentTermField term) assignments)
      unassignedFieldSet = Set.difference fieldSet assignedFieldSet
  in
      if Set.size unassignedFieldSet == 0 then [] else (case pos of (SourcePos' pos) -> [TypeError ("Constructor does not assign values to all fields: "++show signature) pos]; CompiledCode -> [])

getAssignmentTermField :: Term -> Maybe P.SimpleName
getAssignmentTermField (Application (Value (Variable _ target)) (FieldAccess _ fieldName)) = if target == P.createNameThis then Just fieldName else Nothing
getAssignmentTermField (Application innerApplication@(Application _ _) _) = getAssignmentTermField innerApplication
getAssignmentTermField _ = Nothing
