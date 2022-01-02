{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module TypeChecker
  ( typeCheck
  , TypeError
  , transform
  , TypedAbstraction(..)
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
  ) where

import Control.Monad.Trans.State.Strict (StateT,get,put,evalStateT)
import Control.Monad.Trans.Reader (ReaderT, runReaderT, ask)
import Control.Monad (join,foldM,liftM,liftM2)
import Control.Monad.Trans.Class (lift)
import Control.Applicative ( Alternative((<|>)) )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Either as Either
import qualified Data.Maybe as Maybe
import qualified Data.Text as T
import TextShow
import Data.Word
import qualified Parser as P
import Environment
import ClassPath (ClassPath)
import qualified TypeInfo as TI
import Text.ParserCombinators.Parsec (SourcePos)
import Debug.Trace
import qualified Data.Sequence.Internal.Sorting as P
import Data.Maybe (mapMaybe)
import Data.Int (Int32)
import Parser2

type ClassData = (ClassPath,LocalClasses)

data TypedAbstraction = TypedFieldAccess {fName :: P.SimpleName, fTyp :: Type}
                      | TypedMethodInvocation {mName :: P.SimpleName, mTyp :: Type, mParamTyps :: [Type], mTerms :: [TypedTerm]}
                      deriving Show

data TypedValue = TypedVariable {vPosition :: Word8, vTyp :: Type}
                | TypedTypeName {tnTyp :: P.QualifiedName  }
                | TypedIntegerLiteral {iValue :: Int32, iTyp :: P.QualifiedName }
                | TypedStringLiteral {sValue :: String, sTyp :: P.QualifiedName}
                | TypedBooleanLiteral {bValue :: Bool, bTyp :: P.QualifiedName}
                | TypedObjectCreation {ocTyp :: P.QualifiedName, ocParamTyps :: [Type], ocTerms :: [TypedTerm]}
                | TypedCast {cTyp :: P.QualifiedName,  cTerm :: TypedTerm}
                deriving Show

data TypedTerm = TypedValue TypedValue | TypedApplication TypedReferenceTerm TypedAbstraction deriving Show

data TypedReferenceTerm = TypedReferenceTerm P.QualifiedName TypedTerm deriving Show

data TypedConstructorInvocation = NewTypedConstructorInvocation P.QualifiedName [Type] [TypedTerm] deriving Show

data TypedAssignment = NewTypedAssignment TypedTerm TypedTerm deriving Show

data TypedMethod = NewTypedMethod P.SimpleName [Parameter] P.QualifiedName TypedMethodImplementation deriving Show

data TypedClazz = NewTypedClazz P.QualifiedName Extends [Field] [TypedMethod]

data TypedMethodImplementation = TypedMethodImpl TypedTerm | TypedConstructorImpl TypedConstructorInvocation [TypedAssignment] deriving Show

data TypeError = TypeError String SourcePos

instance Show TypeError where
  show (TypeError str pos) = str ++ "\nat: " ++ show pos

getTypedTermType :: TypedTerm -> Type
getTypedTermType (TypedValue TypedVariable {vTyp=tp}) = tp
getTypedTermType (TypedValue TypedTypeName {tnTyp=tp}) = L tp
getTypedTermType (TypedValue TypedIntegerLiteral {iTyp=tp}) = L tp
getTypedTermType (TypedValue TypedStringLiteral {sTyp=tp}) = L tp
getTypedTermType (TypedValue TypedBooleanLiteral {bTyp=tp}) = L tp
getTypedTermType (TypedValue TypedObjectCreation {ocTyp=tp}) = L tp
getTypedTermType (TypedValue TypedCast {cTyp=tp}) = L tp
getTypedTermType (TypedApplication _ TypedFieldAccess {fTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedMethodInvocation {mTyp=tp}) = tp

typeCheck :: StateT ClassData IO (Maybe [TypeError])
typeCheck =
  checkForDuplicateTypeErrors <|> checkForDeclaredTypeErrors <|> checkForClassInheritenceCycles <|> checkForConstructorsUnassignedFieldErrors

transform :: StateT ClassData IO (Either [TypeError] [TypedClazz])
transform = do
  typeData@(_,classMap) <- get
  clazzList <- foldM (\list cls -> (list ++) <$> fmap (: []) (getTypedClazz cls)) [] classMap
  let (typeErrors, typedClazzs) = Either.partitionEithers clazzList
  if not (null typeErrors)
    then return $ Left (concat typeErrors)
    else return $ Right typedClazzs

checkForDuplicateTypeErrors :: StateT ClassData IO (Maybe [TypeError])
checkForDuplicateTypeErrors = do
  typeData@(_,classMap) <- get
  let errors = foldr (\cls list -> getDuplicateFields cls ++ getDuplicateMethods cls ++ list) ([] :: [TypeError]) classMap
  return $ case errors of
    [] -> Nothing
    _ -> Just errors

checkForDeclaredTypeErrors :: StateT ClassData IO (Maybe [TypeError])
checkForDeclaredTypeErrors  = do
  typeData@(_,classMap) <- get
  errors <- foldM (\list cls -> getClassDeclaredTypeErrors cls >>=
              (\l -> (l ++) <$> getFieldDeclaredTypeErrors cls) >>=
              (\l -> (l ++) <$> getMethodsDeclaredTypeErrors cls) ) [] classMap
  case errors of
    [] -> return Nothing 
    _ -> return (Just errors)

checkForClassInheritenceCycles :: StateT ClassData IO (Maybe [TypeError])
checkForClassInheritenceCycles = checkForErrors getClassInheritenceCycleErrors

checkForConstructorsUnassignedFieldErrors :: StateT ClassData IO (Maybe [TypeError])
checkForConstructorsUnassignedFieldErrors = checkForErrors getConstructorsUnassignedFieldErrors

checkForErrors :: (Clazz2 -> StateT ClassData IO [TypeError]) -> StateT ClassData IO (Maybe [TypeError])
checkForErrors getErrorsFunction = do
  typeData@(_,classMap) <- get
  errors <- foldM (\list cls -> (list ++) <$> getErrorsFunction cls) [] classMap
  return $ case errors of
    [] -> Nothing
    _ -> Just errors

getType :: Term -> ReaderT Environment (StateT ClassData IO) (Either [TypeError] TypedTerm)
getType (Value (Variable pos x)) = do
  env <- ask
  return $ case env !? x of Just (tp,ndx) -> Right (TypedValue (TypedVariable {vPosition=fromIntegral ndx :: Word8,vTyp=tp})); Nothing -> Left [TypeError ("Undefined variable: "++show x) pos]
getType (Value (TypeName pos tp)) = do
  env <- ask
  return $ Right (TypedValue (TypedTypeName {tnTyp=tp}))
getType (Value (IntegerLit pos v)) = do
  return $ Right (TypedValue (TypedIntegerLiteral {iValue=v, iTyp=P.createQNameInteger}))
getType (Value (StringLit pos s)) = do
  return $ Right (TypedValue (TypedStringLiteral {sValue=s, sTyp=P.createQNameString}))
getType (Value (BooleanLit pos b)) = do
  return $ Right (TypedValue (TypedBooleanLiteral {bValue=b, bTyp=P.createQNameBoolean}))
getType (Value (ObjectCreation pos tp params)) = do
  typeData <- lift get
  eitherCreateClass <- lift $ TI.getClassTypeInfo tp
  case eitherCreateClass of
    Left _ -> return (Left [TypeError ("Undefined type: "++show tp) pos])
    Right createClass -> do
      eitherParamTypes <- mapM getType params
      if null (Either.lefts eitherParamTypes) then do
        let paramTerms = Either.rights eitherParamTypes
        let signature = Signature P.createNameInit (fmap getTypedTermType paramTerms)
        maybeMethodInvocationExists <- lift $ TI.getMethodType createClass signature
        case maybeMethodInvocationExists of
          Nothing -> return (Left [TypeError ("Undefined constructor: "++show tp++"."++show signature) pos])
          Just (NewMethodInvocation _ (Signature _ targetParamTypes)) -> do
            return (Right (TypedValue (TypedObjectCreation {ocTyp=tp, ocParamTyps=targetParamTypes,ocTerms=paramTerms})))
      else return $ Left (concat (Either.lefts eitherParamTypes))
getType (Value (Cast pos tp t)) = do
  typeData <- lift get
  eitherTypedTerm <- getType t
  case eitherTypedTerm of
    Left _ -> return eitherTypedTerm
    Right typedTerm -> do
      eitherTermTypeInfo <- lift $ TI.getClassTypeInfo (TI.getBoxedType (getTypedTermType typedTerm))
      eitherCastTypeInfo <- lift $ TI.getClassTypeInfo tp
      isSubtype <- lift $TI.isSubtypeOf eitherCastTypeInfo eitherTermTypeInfo
      case isSubtype of
        Left txt -> return $ Left [TypeError ("Undefined type: "++T.unpack txt) pos]
        Right b -> if b
          then return $ Right (TypedValue (TypedCast {cTyp=tp, cTerm=typedTerm}))
          else return $ Left [TypeError ("Invalid cast: "++show tp) pos]
getType (Application t (FieldAccess pos nm)) = do
  typeData <- lift get
  eitherTypedTerm <- getType t
  case eitherTypedTerm of
    Left _ -> return eitherTypedTerm
    Right typedTerm -> do
      case getTypedTermType typedTerm of
        I -> return $ Left [TypeError "int cannot be dereferenced" pos]
        Z -> return $ Left [TypeError "boolean cannot be dereferenced" pos]
        L termTypeName -> do
          eitherTermType <- lift $ TI.getClassTypeInfo termTypeName
          case eitherTermType of
            Left txt -> return $ Left [TypeError ("Undefined type: "++T.unpack txt) pos]
            Right termType -> do
              maybeFieldType <- getFieldType nm termType
              case maybeFieldType of
                Nothing -> return $ Left [TypeError ("Undefined field: "++show nm) pos]
                Just tp -> return $ Right (TypedApplication (TypedReferenceTerm termTypeName typedTerm) (TypedFieldAccess {fName=nm,fTyp=tp}))
        Unsupported tp -> return $ Left [TypeError "unsupported primitive type cannot be dereferenced" pos]

getType (Application t (MethodInvocation pos nm params)) = do
  typeData <- lift get
  eitherTypedTerm <- getType t
  eitherParamTypes <- mapM getType params
  if null (Either.lefts eitherParamTypes) then do
    let paramTypedTerms = Either.rights eitherParamTypes
    let signature = Signature nm (fmap getTypedTermType paramTypedTerms)
    case eitherTypedTerm of
      Left _ -> return eitherTypedTerm
      Right typedTerm ->
        case getTypedTermType typedTerm of
          I -> return $ Left [TypeError "int cannot be dereferenced" pos]
          Z -> return $ Left [TypeError "boolean cannot be dereferenced" pos]
          L termTypeName -> do
            eitherTermType <- lift $ TI.getClassTypeInfo termTypeName
            case eitherTermType of
              Left txt -> return $ Left [TypeError ("Undefined type: "++T.unpack txt) pos]
              Right termType -> do
                maybeMethodType <- if isStaticContext typedTerm
                  then getStaticMethodType signature termType
                  else getMethodType signature termType
                case maybeMethodType of
                  Nothing -> return (Left [TypeError ("Undefined method: "++show termTypeName++":"++show signature) pos])
                  Just (NewMethodInvocation targetType (Signature _ targetParamTypes)) -> return
                    (Right (TypedApplication
                      (TypedReferenceTerm termTypeName typedTerm)
                      (TypedMethodInvocation {mName=nm,mTyp=targetType,mParamTyps=targetParamTypes,mTerms=paramTypedTerms})))
          Unsupported tp -> return $ Left [TypeError "unsupported primitive type cannot be dereferenced" pos]
  else return $ Left (concat (Either.lefts eitherParamTypes))

getFieldType :: P.SimpleName -> TI.TypeInfo -> ReaderT Environment (StateT ClassData IO) (Maybe Type)
getFieldType nm tp = do
  typeData <- lift get
  let maybeFieldType = TI.getFieldType tp nm
  case maybeFieldType of
    Just _ -> return maybeFieldType
    Nothing ->
      let parentName = TI.getTypeParent tp
      in
        if parentName == P.createQNameObject
          then return Nothing
          else do
            eitherParentType <- lift $ TI.getClassTypeInfo parentName
            case eitherParentType of
              Left txt -> undefined -- This should never happen
              Right parentType -> getFieldType nm parentType

getMethodType :: Signature -> TI.TypeInfo -> ReaderT Environment (StateT ClassData IO) (Maybe MethodInvocation)
getMethodType signature tp = do
  typeData <- lift get
  maybeMethodType <- lift $ TI.getMethodType tp signature
  case maybeMethodType of
    Just _ -> return maybeMethodType
    Nothing ->
      if TI.getTypeName tp == P.createQNameObject
        then return Nothing
        else do
        let parentName = TI.getTypeParent tp
        eitherParentType <- lift $ TI.getClassTypeInfo parentName
        case eitherParentType of
          Left txt -> undefined -- This should never happen
          Right parentType -> getMethodType signature parentType

getStaticMethodType :: Signature -> TI.TypeInfo -> ReaderT Environment (StateT ClassData IO) (Maybe MethodInvocation)
getStaticMethodType signature tp = do
  typeData <- lift get
  lift $ TI.getStaticMethodType tp signature

isStaticContext :: TypedTerm -> Bool
isStaticContext (TypedValue (TypedTypeName _)) = True
isStaticContext (TypedApplication (TypedReferenceTerm _ term') _) = isStaticContext term'
isStaticContext _ = False

getDuplicateFields :: Clazz2 -> [TypeError]
getDuplicateFields (NewClazz2 _ _ _ _ fields _) =
  snd $ foldr (\field@(NewField pos tp _ nm) (fieldMap, duplicateList) ->
    (case Map.lookup nm fieldMap of
      Nothing -> (Map.insert nm nm fieldMap, duplicateList)
      Just _ -> (fieldMap, TypeError ("Duplicate field: "++show nm) pos:duplicateList)))
    (Map.empty, [])
    fields

getDuplicateMethods :: Clazz2 -> [TypeError]
getDuplicateMethods (NewClazz2 _ _ _ _ _ methods) =
  snd $ foldr (\method@(NewMethod pos _ _ _ sig@(Signature nm params) _) (methodMap, duplicateList) ->
    (case Map.lookup nm methodMap of
      Nothing -> (Map.insert nm [params] methodMap, duplicateList)
      Just paramsList -> if params `elem` paramsList
        then (methodMap, TypeError ("Duplicate method: "++show sig) pos:duplicateList)
        else (Map.update (\l -> Just (params:l)) nm methodMap, duplicateList)))
    (Map.empty, [])
    methods

getClassDeclaredTypeErrors :: Clazz2 -> StateT ClassData IO [TypeError]
getClassDeclaredTypeErrors (NewClazz2 _ _ _ ExtendsObject _ _) = return []
getClassDeclaredTypeErrors (NewClazz2 _ _ _ (NewExtends pos parent) _ _) = do
  typeData <- get
  lift $ do
           let cond =  TI.isValidClass typeData parent
           return $ [TypeError ("Undefined type: "++show parent) pos | not cond]

getFieldDeclaredTypeErrors :: Clazz2 -> StateT ClassData IO [TypeError]
getFieldDeclaredTypeErrors (NewClazz2 _ _ _ _ fields _) = do
  typeData <- get
  lift $ foldM (\errorList field@(NewField pos tp _ _) ->
    do
      let cond = TI.isValidClass typeData tp
      return $ if cond then errorList else TypeError ("Undefined type: "++show tp) pos:errorList)
    []
    fields

getMethodsDeclaredTypeErrors :: Clazz2 -> StateT ClassData IO [TypeError]
getMethodsDeclaredTypeErrors (NewClazz2 _ _ _ _ _ methods) =
  foldM (\errorList method -> fmap (++ errorList) (getMethodDeclaredTypeErrors method)) [] methods

getMethodDeclaredTypeErrors :: Method -> StateT ClassData IO [TypeError]
getMethodDeclaredTypeErrors method = do
  returnDeclaredTypeErrors <- getMethodReturnDeclaredTypeErrors method
  paramDeclaredTypeErrors <- getMethodParamDeclaredTypeErrors method
  expressionDeclaredTypeErrors <- getMethodExpressionDeclaredTypeErrors method
  return $ returnDeclaredTypeErrors ++ paramDeclaredTypeErrors ++ expressionDeclaredTypeErrors

getMethodReturnDeclaredTypeErrors :: Method -> StateT ClassData IO [TypeError]
getMethodReturnDeclaredTypeErrors (NewMethod pos _ _ tp _ _) = do
  typeData <- get
  lift $ do
           let cond = TI.isValidClass typeData tp
           return $ [TypeError ("Undefined type: "++show tp) pos | not cond]

getMethodParamDeclaredTypeErrors :: Method -> StateT ClassData IO [TypeError]
getMethodParamDeclaredTypeErrors (NewMethod _ _ params _ _ _) =
  getParamDeclaredTypeErrors params

getMethodExpressionDeclaredTypeErrors :: Method -> StateT ClassData IO [TypeError]
getMethodExpressionDeclaredTypeErrors (NewMethod _ _ _ _ _ (MethodImpl term)) =
  getTermDeclaredTypeErrors term
getMethodExpressionDeclaredTypeErrors (NewMethod _ _ _ _ _ (ConstructorImpl maybeConstructorInvocation assignments)) =
  getAssignmentsDeclaredTypeErrors assignments

getParamDeclaredTypeErrors :: [Parameter] -> StateT ClassData IO [TypeError]
getParamDeclaredTypeErrors params = do
  typeData <- get
  lift $ foldM (\errorList (NewParameter pos tp _) ->
    do
      let cond = TI.isValidClass typeData tp
      return $ if cond then errorList else TypeError ("Undefined type: "++show tp) pos:errorList)
    []
    params

getAssignmentsDeclaredTypeErrors :: [Assignment]-> StateT ClassData IO [TypeError]
getAssignmentsDeclaredTypeErrors = foldM (\errorList a -> fmap (++ errorList) (getAssignmentDeclaredTypeErrors a)) []

getAssignmentDeclaredTypeErrors :: Assignment -> StateT ClassData IO [TypeError]
getAssignmentDeclaredTypeErrors (NewAssignment pos t1 t2) = do
  t1errors <- getTermDeclaredTypeErrors t1
  t2errors <- getTermDeclaredTypeErrors t2
  return (t1errors ++ t2errors)

getTermDeclaredTypeErrors :: Term -> StateT ClassData IO [TypeError]
getTermDeclaredTypeErrors t = do
  typeData <- get
  case t of
    (Value (ObjectCreation pos tp params)) -> liftM2 (++) paramErrors classError
      where
        classError = lift $ do let cond = TI.isValidClass typeData tp in return $ [TypeError ("Undefined type: "++show tp) pos | not cond]
        paramErrors = foldM (\errs t' -> fmap (++ errs) (getTermDeclaredTypeErrors t')) [] params
    (Value (Cast pos tp term)) -> liftM2 (++) termError classError
      where
        classError = lift $ do let cond = TI.isValidClass typeData tp in return $ [TypeError ("Undefined type: "++show tp) pos | not cond]
        termError = getTermDeclaredTypeErrors term
    (Application t' (FieldAccess _ _)) -> getTermDeclaredTypeErrors t'
    (Application t' (MethodInvocation pos nm params)) ->  liftM2 (++) paramErrors termErrors
      where
        termErrors = getTermDeclaredTypeErrors t'
        paramErrors = foldM (\errs t'' -> fmap (++ errs) (getTermDeclaredTypeErrors t'')) [] params
    _ -> return []

getClassInheritenceCycleErrors :: Clazz2 -> StateT ClassData IO [TypeError]
getClassInheritenceCycleErrors clazz = getClassInheritenceCycleErrors' clazz []

getClassInheritenceCycleErrors' :: Clazz2 -> [P.QualifiedName] -> StateT ClassData IO [TypeError]
getClassInheritenceCycleErrors' (NewClazz2 _ _ _ ExtendsObject _ _) _ = return []
getClassInheritenceCycleErrors' (NewClazz2 _ _ nm (NewExtends pos parent) _ _) classes = do
  (_,classMap) <- get
  if parent `elem` classes
    then return [TypeError ("Cyclic Inheritence: "++show nm) pos]
    else if Map.member parent classMap
      then getClassInheritenceCycleErrors' (classMap Map.! parent) (parent : classes)
      else return []

getTypedClazz :: Clazz2 -> StateT ClassData IO (Either [TypeError] TypedClazz)
getTypedClazz cls@(NewClazz2 _ _ name extends fields _) = do
  eitherMorE <- getMethodsTermTypeErrors cls
  return $ case eitherMorE of
      Left methodErrors -> Left methodErrors;
      Right typedMethods -> Right (NewTypedClazz name extends fields typedMethods)

getMethodsTermTypeErrors :: Clazz2 -> StateT ClassData IO (Either [TypeError] [TypedMethod])
getMethodsTermTypeErrors cls@(NewClazz2 _ _ nm _ _ methods) = do
  typeData <- get
  eitherList <-  mapM (getMethodTermTypeErrors cls) methods
  let (errorList, typedMethodList) = Either.partitionEithers eitherList
  return $ if not (null errorList) then Left (concat errorList) else Right typedMethodList

getMethodTermTypeErrors :: Clazz2 -> Method -> StateT ClassData IO (Either [TypeError] TypedMethod)
getMethodTermTypeErrors cls method@(NewMethod pos nm params tp _ (MethodImpl t)) = do
  typeData <- get
  let methodEnvironment = createMethodEnvironment typeData cls method
  eitherTypedTerm <- runReaderT (getType t) methodEnvironment
  case eitherTypedTerm of
    Left e -> return $ Left e
    Right typedTerm -> if tp == TI.getBoxedType (getTypedTermType typedTerm)
      then return $ Right (NewTypedMethod nm params tp (TypedMethodImpl typedTerm));
      else return $ Left [TypeError ("Incorrect return type: "++show (getTypedTermType typedTerm)) pos]
getMethodTermTypeErrors cls@(NewClazz2 _ _ _ extends _ _) method@(NewMethod pos nm params tp _ (ConstructorImpl maybeConstructorInvocation assignments)) = do
  typeData <- get
  let constructorRightEnvironment = createConstructorEnvironmentRight typeData cls method
  let constructorLeftEnvironment = createConstructorEnvironmentLeft typeData cls
  maybeEitherC <- case maybeConstructorInvocation of
    Just ci -> do
      eitherTypedCI <- runReaderT (getTypedConstructorInvocation cls ci) constructorRightEnvironment
      case eitherTypedCI of
        Left e -> return $ Just $ Left e
        Right typedCI -> return $ Just $ Right typedCI
    Nothing -> return Nothing
  eitherList <- mapM (getAssignmentTypeError constructorLeftEnvironment constructorRightEnvironment) assignments
  let (assignmentTypeErrors,typedAssignments) = Either.partitionEithers eitherList
  case maybeEitherC of
    Just eitherC ->
      case eitherC of
        Left le -> return $ Left (le ++ concat assignmentTypeErrors)
        Right ci -> if not (null assignmentTypeErrors)
          then return $ Left (concat assignmentTypeErrors)
          else return $ Right (NewTypedMethod P.createNameInit params P.createQNameObject (TypedConstructorImpl ci typedAssignments))
    Nothing ->
      if not (null assignmentTypeErrors)
        then return $ Left (concat assignmentTypeErrors)
        else do 
          return $ case extends of
            NewExtends _ qn -> Right (NewTypedMethod 
              P.createNameInit 
              params 
              P.createQNameObject 
              (TypedConstructorImpl (defaultConstructorInvocation qn)  typedAssignments))
            ExtendsObject -> Right (NewTypedMethod 
              P.createNameInit 
              params 
              P.createQNameObject 
              (TypedConstructorImpl (defaultConstructorInvocation P.createQNameObject)  typedAssignments))
          

defaultConstructorInvocation :: P.QualifiedName -> TypedConstructorInvocation
defaultConstructorInvocation parentCls = NewTypedConstructorInvocation parentCls [] []

getAssignmentTypeError :: Environment -> Environment -> Assignment -> StateT ClassData IO (Either [TypeError] TypedAssignment)
getAssignmentTypeError lenv renv (NewAssignment pos leftTerm rightTerm) = do
  typeData <- get
  leftTermType <- runReaderT (getType leftTerm) lenv
  rightTermType <- runReaderT (getType rightTerm) renv
  case leftTermType of
    Left le -> case rightTermType of
      Left re -> return $ Left (le++re)
      Right _ -> return $ Left le
    Right ltp ->
      case rightTermType of
        Left re -> return $ Left re
        Right rtp -> do
          eitherrti <- TI.getClassTypeInfo (TI.getBoxedType (getTypedTermType rtp))
          eitherlti <- TI.getClassTypeInfo (TI.getBoxedType (getTypedTermType ltp))
          eitherIsSubtype <- TI.isSubtypeOf eitherrti eitherlti
          case eitherIsSubtype of
            Left txt -> return $ Left [TypeError ("Undefined type: "++T.unpack txt) pos]
            Right isSubtype -> if isTermValidForLeftAssignment leftTerm && isSubtype
              then return $ Right (NewTypedAssignment ltp rtp)
              else return $ Left [TypeError "Illegal assignment" pos]

isTermValidForLeftAssignment :: Term -> Bool
isTermValidForLeftAssignment (Application (Value (Variable _ target)) (FieldAccess _ _)) = P.createNameThis == target
isTermValidForLeftAssignment (Application t (FieldAccess _ _)) = isTermValidForLeftAssignment t
isTermValidForLeftAssignment t = False

getTypedConstructorInvocation ::  Clazz2 -> ConstructorInvocation -> ReaderT Environment (StateT ClassData IO) (Either [TypeError] TypedConstructorInvocation)
getTypedConstructorInvocation  cls@(NewClazz2 _ _ tp extends _ _) (NewConstructorInvocation pos terms) = do
  constructorSuperInvocationEnvironment <- ask
  eitherTermTypes <- mapM getType terms
  if null (Either.lefts eitherTermTypes) then
    let termTypes = Either.rights eitherTermTypes
        signature = Signature P.createNameInit (fmap getTypedTermType termTypes) in
        case extends of
          (NewExtends _ parentClass) -> do
            eitherParentTypeInfo <- lift $ TI.getClassTypeInfo parentClass
            case eitherParentTypeInfo of
              Left txt -> return $ Left [TypeError ("Undefined type: "++show parentClass) pos]
              Right parentTypeInfo -> do
                maybeSuperConstructor <- getMethodType signature parentTypeInfo
                case maybeSuperConstructor of
                  Nothing -> return $ Left [TypeError ("No invocation compatible constructor: "++show tp++"."++show signature) pos]
                  Just (NewMethodInvocation _ (Signature _ targetTermTypes)) -> 
                    return $ Right (NewTypedConstructorInvocation parentClass targetTermTypes termTypes)
          ExtendsObject -> return $ Right (NewTypedConstructorInvocation P.createQNameObject [] [])
  else return $ Left (concat (Either.lefts eitherTermTypes))

getConstructorsUnassignedFieldErrors :: Clazz2 -> StateT ClassData IO [TypeError]
getConstructorsUnassignedFieldErrors cls@(NewClazz2 _ _ nm _ _ methods) = do
  let constructors = filter (\(NewMethod _ nm _ _ _ _) -> nm == P.createNameInit)  methods
  return $ foldr (\c list -> getConstructorUnassignedFieldError cls c ++ list) [] constructors

getConstructorUnassignedFieldError :: Clazz2 -> Method -> [TypeError]
getConstructorUnassignedFieldError cls@(NewClazz2 _ _ clsNm _ fields _) constructor@(NewMethod pos _ _ _ signature (ConstructorImpl _ assignments)) =
  let fieldSet = Set.fromList (fmap (\(NewField _ _ _ nm) -> nm) fields)
      assignedFieldSet = Set.fromList (mapMaybe (\(NewAssignment _ term _) -> getAssignmentTermField term) assignments)
      unassignedFieldSet = Set.difference fieldSet assignedFieldSet
  in
      if Set.size unassignedFieldSet == 0 then [] else [TypeError ("Constructor does not assign values to all fields: "++show signature) pos]

getAssignmentTermField :: Term -> Maybe P.SimpleName
getAssignmentTermField (Application (Value (Variable _ target)) (FieldAccess _ fieldName)) = if target == P.createNameThis then Just fieldName else Nothing
getAssignmentTermField (Application innerApplication@(Application _ _) _) = getAssignmentTermField innerApplication
getAssignmentTermField _ = Nothing
