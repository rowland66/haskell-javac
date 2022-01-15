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
  , TypeName
  ) where

import Control.Monad.Trans.State.Strict (StateT,get,put,evalStateT)
import Control.Monad.Trans.Reader (ReaderT, runReaderT, ask)
import Control.Monad (join,foldM,liftM,liftM2)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except ( ExceptT, runExceptT, throwE )
import Control.Monad.Extra (ifM)
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

data TypedAbstraction = TypedFieldAccess {fName :: P.SimpleName, fTyp :: TI.Type}
                      | TypedMethodInvocation {mName :: P.SimpleName, mTyp :: TI.Type, mParamTyps :: [TI.Type], mTerms :: [TypedTerm]}
                      deriving Show

data TypedValue = TypedVariable {vPosition :: Word8, vTyp :: TI.Type}
                | TypedIntegerLiteral {iValue :: Int32 }
                | TypedStringLiteral {sValue :: String }
                | TypedBooleanLiteral {bValue :: Bool }
                | TypedObjectCreation {ocTyp :: P.QualifiedName, ocParamTyps :: [TI.Type], ocTerms :: [TypedTerm]}
                deriving Show

data TypedTerm = TypedValue TypedValue
               | TypedApplication TypedReferenceTerm TypedAbstraction
               | TypedStaticApplication TypeName TypedAbstraction
               | TypedCast TypedReferenceTerm
               | TypedConditional TypedTerm TypedTerm TypedTerm TI.Type
               deriving Show

data TypedReferenceTerm = TypedReferenceTerm P.QualifiedName TypedTerm deriving Show

data TypedConstructorInvocation = NewTypedConstructorInvocation P.QualifiedName [TI.Type] [TypedTerm] deriving Show

data TypedAssignment = NewTypedAssignment TypedTerm TypedTerm deriving Show

data TypedMethod = NewTypedMethod P.SimpleName [Parameter] P.QualifiedName TypedMethodImplementation deriving Show

data TypedClazz = NewTypedClazz P.QualifiedName Extends [Field] [TypedMethod]

data TypedMethodImplementation = TypedMethodImpl TypedTerm 
                               | TypedConstructorImpl TypedConstructorInvocation [TypedAssignment] 
                               deriving Show

init' = T.pack "<init>"

getTypedTermType :: TypedTerm -> TI.Type
getTypedTermType (TypedValue TypedVariable {vTyp=tp}) = tp
getTypedTermType (TypedValue TypedIntegerLiteral {}) = TI.L P.createQNameInteger CompiledCode
getTypedTermType (TypedValue TypedStringLiteral {}) = TI.L P.createQNameString CompiledCode
getTypedTermType (TypedValue TypedBooleanLiteral {}) = TI.L P.createQNameBoolean CompiledCode
getTypedTermType (TypedValue TypedObjectCreation {ocTyp=tp}) = TI.L tp CompiledCode
getTypedTermType (TypedApplication _ TypedFieldAccess {fTyp=tp}) = tp
getTypedTermType (TypedApplication _ TypedMethodInvocation {mTyp=tp}) = tp
getTypedTermType (TypedStaticApplication _ TypedFieldAccess {fTyp=tp}) = tp
getTypedTermType (TypedStaticApplication _ TypedMethodInvocation {mTyp=tp}) = tp
getTypedTermType (TypedCast (TypedReferenceTerm tp _)) = TI.L tp CompiledCode
getTypedTermType (TypedConditional _ _ _ t) = t

typeCheck :: StateT ClassData IO (Maybe [TypeError])
typeCheck =
  checkForDuplicateTypeErrors <|> checkForDeclaredTypeErrors <|> checkForClassInheritenceCycles <|> checkForConstructorsUnassignedFieldErrors

transform :: StateT ClassData IO (Either [TypeError] [TypedClazz])
transform = do
  typeData@(_,classMap) <- get
  clazzList <- foldM (\list cls -> (list ++) <$> fmap (: []) (runExceptT (getTypedClazz cls))) [] classMap
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

getType :: Term -> ReaderT Environment (ExceptT [TypeError] (StateT ClassData IO)) TypedTerm
getType (Value (Variable pos x)) = do
  env <- ask
  case env !? x of Just (tp,ndx) -> return $ TypedValue (TypedVariable {vPosition=fromIntegral ndx :: Word8,vTyp=tp}); Nothing -> lift $ throwE [TypeError ("Undefined variable: "++show x) (SourcePos' pos)]
getType (Value (IntegerLit pos v)) = do
  return $ TypedValue (TypedIntegerLiteral {iValue=v})
getType (Value (StringLit pos s)) = do
  return $ TypedValue (TypedStringLiteral {sValue=s})
getType (Value (BooleanLit pos b)) = do
  return $ TypedValue (TypedBooleanLiteral {bValue=b})
getType (Value (ObjectCreation pos (TypeName tpos tp) params)) = do
  typeData <- lift $ lift get
  createClass <- lift $ TI.getClassTypeInfoE (tp,SourcePos' tpos)
  paramTerms <- mapM getType params
  let signature = TI.ClassPathSignature init' (fmap getTypedTermType paramTerms)
  maybeMethodInvocationExists <- lift $ TI.getMethodType createClass signature
  case maybeMethodInvocationExists of
    Nothing -> lift $ throwE [TypeError ("No matching constructor: "++show tp++"."++show signature) (SourcePos' pos)]
    Just (TI.NewMethodInvocation _ (TI.ClassPathSignature _ targetParamTypes)) -> do
      return (TypedValue (TypedObjectCreation {ocTyp=tp, ocParamTyps=targetParamTypes,ocTerms=paramTerms}))
getType (Cast (TypeName pos tp) t) = do
  typeData <- lift $ lift get
  typedTerm <- getType t
  let typedTermType = getTypedTermType typedTerm
  termTypeInfo <- lift $ TI.getClassTypeInfoE (TI.getBoxedType (getTypedTermType typedTerm))
  castTypeInfo <- lift $ TI.getClassTypeInfoE (tp, SourcePos' pos)
  isSubtype <- lift $ TI.isSubtypeOf' castTypeInfo termTypeInfo
  if isSubtype
    then return (TypedCast (TypedReferenceTerm tp typedTerm))
    else lift $ throwE [TypeError ("Invalid cast: "++show tp) (SourcePos' pos)]
getType (Application t (FieldAccess pos nm)) = do
  typeData <- lift $ lift get
  typedTerm <- getType t
  case getTypedTermType typedTerm of
    TI.I _-> lift $ throwE [TypeError "int cannot be dereferenced" (SourcePos' pos)]
    TI.Z _-> lift $ throwE [TypeError "boolean cannot be dereferenced" (SourcePos' pos)]
    TI.L termTypeName pos -> do
      termType <- lift $ TI.getClassTypeInfoE (termTypeName,pos)
      maybeFieldType <- lift $ getFieldType nm termType
      case maybeFieldType of
        Nothing -> lift $ throwE [TypeError ("Undefined field: "++show nm) pos]
        Just tp -> return (TypedApplication (TypedReferenceTerm termTypeName typedTerm) (TypedFieldAccess {fName=nm,fTyp=tp}))
    TI.UnsupportedType pos -> lift $ throwE [TypeError "unsupported primitive type cannot be dereferenced" pos]
getType (Application t (MethodInvocation pos nm params)) = do
  typedTerm <- getType t
  paramTerms <- mapM getType params
  let signature = TI.ClassPathSignature (P.deconstructSimpleName nm) (fmap getTypedTermType paramTerms)
  case getTypedTermType typedTerm of
    TI.I _-> lift $ throwE [TypeError "int cannot be dereferenced" (SourcePos' pos)]
    TI.Z _-> lift $ throwE [TypeError "boolean cannot be dereferenced" (SourcePos' pos)]
    TI.L termTypeName pos-> do
      termType <- lift $ TI.getClassTypeInfoE (termTypeName,pos)
      maybeMethodType <- lift $ getMethodType signature termType
      case maybeMethodType of
        Nothing -> lift $ throwE [TypeError ("Undefined method: "++show termTypeName++":"++show signature) pos]
        Just (TI.NewMethodInvocation targetType (TI.ClassPathSignature _ targetParamTypes)) -> return
          (TypedApplication
            (TypedReferenceTerm termTypeName typedTerm)
            (TypedMethodInvocation {mName=nm,mTyp=targetType,mParamTyps=targetParamTypes,mTerms=paramTerms}))
    TI.UnsupportedType pos -> lift $ throwE [TypeError "unsupported primitive type cannot be dereferenced" pos]
getType (StaticApplication tn@(TypeName tnPos tnQn) (FieldAccess pos nm)) = do
    typeNameTypeInfo <- lift $ TI.getClassTypeInfoE (tnQn,SourcePos' tnPos)
    maybeFieldType <- lift $ getFieldType nm typeNameTypeInfo
    case maybeFieldType of
      Nothing -> lift $ throwE [TypeError ("Undefined static field: "++show tnQn++":"++show nm) (SourcePos' pos)]
      Just tp -> return (TypedStaticApplication tn (TypedFieldAccess {fName=nm,fTyp=tp}))
getType (StaticApplication tn@(TypeName tnPos tnQn) (MethodInvocation pos nm params)) = do
  paramTypedTerms <- mapM getType params
  let signature = TI.ClassPathSignature (P.deconstructSimpleName nm) (fmap getTypedTermType paramTypedTerms)
  typeNameTypeInfo <- lift $ TI.getClassTypeInfoE (tnQn,SourcePos' tnPos)
  maybeMethodInvocation <- lift $ TI.getStaticMethodType typeNameTypeInfo signature
  case maybeMethodInvocation of
    Nothing -> lift $ throwE [TypeError ("Undefined static method: "++show tnQn++":"++show signature) (SourcePos' pos)]
    Just (TI.NewMethodInvocation targetType (TI.ClassPathSignature _ targetParamTypes)) -> return
      (TypedStaticApplication
        tn (TypedMethodInvocation {mName=nm,mTyp=targetType,mParamTyps=targetParamTypes,mTerms=paramTypedTerms}))
getType (Conditional b1 t1 t2) = do
  booleanExpr <- getType b1
  term1 <- getType t1
  term2 <- getType t2
  if not (TI.isTypeBoolean (TI.getUnboxedType (getTypedTermType booleanExpr)))
    then lift $ throwE [TypeError "First term in conditional is not boolean" (SourcePos' (getTermPosition b1))]
    else do
      case (getTypedTermType term1, getTypedTermType term2) of
        (tp@(TI.L qn1 _),TI.L qn2 _) | qn1 == qn2 -> return $ TypedConditional booleanExpr term1 term2 tp
        (t1, t2) | TI.isTypeBoolean (TI.getUnboxedType t1)
                && TI.isTypeBoolean (TI.getUnboxedType t2) ->
                   return $ TypedConditional booleanExpr term1 term2 (TI.Z CompiledCode)
        (t1, t2) | TI.isTypeInteger (TI.getUnboxedType t1)
                && TI.isTypeInteger (TI.getUnboxedType t2) ->
                   return $ TypedConditional booleanExpr term1 term2 (TI.I CompiledCode)
        (t1, t2) -> do
          lub <- lift $ leastUpperBound [fst (TI.getBoxedType t1), fst (TI.getBoxedType t2)]
          return $ TypedConditional booleanExpr term1 term2 lub
        {--_ -> lift $ throwE [TypeError "Second and third terms in conditional are different types" (SourcePos' (P2.getTermPosition t2))]--}


getFieldType :: P.SimpleName -> TI.TypeInfo -> ExceptT [TypeError] (StateT ClassData IO) (Maybe TI.Type)
getFieldType nm tp = do
  typeData <- lift get
  let maybeFieldType = TI.getFieldType tp nm
  case maybeFieldType of
    Just _ -> return maybeFieldType
    Nothing ->
      let parentName = TI.getTypeParent tp
      in
        if fst parentName == P.createQNameObject
          then return Nothing
          else do
            parentType <- TI.getClassTypeInfoE parentName
            getFieldType nm parentType

getMethodType :: TI.ClassPathSignature -> TI.TypeInfo -> ExceptT [TypeError] (StateT ClassData IO) (Maybe TI.MethodInvocation)
getMethodType signature tp = do
  typeData <- lift get
  maybeMethodType <- TI.getMethodType tp signature
  case maybeMethodType of
    Just _ -> return maybeMethodType
    Nothing ->
      if fst (TI.getTypeName tp) == P.createQNameObject
        then return Nothing
        else do
        let parentName = TI.getTypeParent tp
        parentType <- TI.getClassTypeInfoE parentName
        getMethodType signature parentType

getDuplicateFields :: Clazz2 -> [TypeError]
getDuplicateFields (NewClazz2 _ _ _ _ fields _) =
  snd $ foldr (\field@(NewField pos tp _ nm) (fieldMap, duplicateList) ->
    (case Map.lookup nm fieldMap of
      Nothing -> (Map.insert nm nm fieldMap, duplicateList)
      Just _ -> (fieldMap, TypeError ("Duplicate field: "++show nm) (SourcePos' pos):duplicateList)))
    (Map.empty, [])
    fields

getDuplicateMethods :: Clazz2 -> [TypeError]
getDuplicateMethods (NewClazz2 _ _ _ _ _ methods) =
  snd $ foldr (\method@(NewMethod pos _ _ _ sig@(Signature nm params) _) (methodMap, duplicateList) ->
    (case Map.lookup nm methodMap of
      Nothing -> (Map.insert nm [params] methodMap, duplicateList)
      Just paramsList -> if params `elem` paramsList
        then (methodMap, TypeError ("Duplicate method: "++show sig) (SourcePos' pos):duplicateList)
        else (Map.update (\l -> Just (params:l)) nm methodMap, duplicateList)))
    (Map.empty, [])
    methods

getClassDeclaredTypeErrors :: Clazz2 -> StateT ClassData IO [TypeError]
getClassDeclaredTypeErrors (NewClazz2 _ _ _ ExtendsObject _ _) = return []
getClassDeclaredTypeErrors (NewClazz2 _ _ _ (NewExtends pos parent) _ _) = do
  typeData <- get
  lift $ do
           let cond =  TI.isValidClass typeData parent
           return $ [TypeError ("Undefined type: "++show parent) (SourcePos' pos) | not cond]

getFieldDeclaredTypeErrors :: Clazz2 -> StateT ClassData IO [TypeError]
getFieldDeclaredTypeErrors (NewClazz2 _ _ _ _ fields _) = do
  typeData <- get
  lift $ foldM (\errorList field@(NewField pos tp _ _) ->
    do
      let cond = TI.isValidClass typeData tp
      return $ if cond then errorList else TypeError ("Undefined type: "++show tp) (SourcePos' pos):errorList)
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
           return $ [TypeError ("Undefined type: "++show tp) (SourcePos' pos) | not cond]

getMethodParamDeclaredTypeErrors :: Method -> StateT ClassData IO [TypeError]
getMethodParamDeclaredTypeErrors (NewMethod _ _ params _ _ _) =
  getParamDeclaredTypeErrors params

getMethodExpressionDeclaredTypeErrors :: Method -> StateT ClassData IO [TypeError]
getMethodExpressionDeclaredTypeErrors (NewMethod _ _ _ _ _ (MethodImpl term)) =
  getTermDeclaredTypeErrors term
getMethodExpressionDeclaredTypeErrors (NewMethod _ _ _ _ _ (ConstructorImpl _ assignments)) =
  getAssignmentsDeclaredTypeErrors assignments

getParamDeclaredTypeErrors :: [Parameter] -> StateT ClassData IO [TypeError]
getParamDeclaredTypeErrors params = do
  typeData <- get
  lift $ foldM (\errorList (NewParameter pos tp _) ->
    do
      let cond = TI.isValidClass typeData tp
      return $ if cond then errorList else TypeError ("Undefined type: "++show tp) (SourcePos' pos):errorList)
    []
    params

getAssignmentsDeclaredTypeErrors :: [Assignment]-> StateT ClassData IO [TypeError]
getAssignmentsDeclaredTypeErrors = foldM (\errorList a -> fmap (++ errorList) (getAssignmentDeclaredTypeErrors a)) []

getAssignmentDeclaredTypeErrors :: Assignment -> StateT ClassData IO [TypeError]
getAssignmentDeclaredTypeErrors (NewAssignment lpos t1 rpos t2) = do
  t1errors <- getTermDeclaredTypeErrors t1
  t2errors <- getTermDeclaredTypeErrors t2
  return (t1errors ++ t2errors)

getTermDeclaredTypeErrors :: Term -> StateT ClassData IO [TypeError]
getTermDeclaredTypeErrors t = do
  typeData <- get
  case t of
    (Value (ObjectCreation pos (TypeName _ tp) params)) -> liftM2 (++) paramErrors classError
      where
        classError = lift $ do let cond = TI.isValidClass typeData tp in return $ [TypeError ("Undefined type: "++show tp) (SourcePos' pos) | not cond]
        paramErrors = foldM (\errs t' -> fmap (++ errs) (getTermDeclaredTypeErrors t')) [] params
    (Cast (TypeName pos tp) term) -> liftM2 (++) termError classError
      where
        classError = lift $ do let cond = TI.isValidClass typeData tp in return $ [TypeError ("Undefined type: "++show tp) (SourcePos' pos) | not cond]
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
    then return [TypeError ("Cyclic Inheritence: "++show nm) (SourcePos' pos)]
    else if Map.member parent classMap
      then getClassInheritenceCycleErrors' (classMap Map.! parent) (parent : classes)
      else return []

getTypedClazz :: Clazz2 -> ExceptT [TypeError] (StateT ClassData IO) TypedClazz
getTypedClazz cls@(NewClazz2 _ _ name extends fields _) = do
  typedMethodList <- getMethodsTermTypeErrors cls
  return $ NewTypedClazz name extends fields typedMethodList

getMethodsTermTypeErrors :: Clazz2 -> ExceptT [TypeError] (StateT ClassData IO) [TypedMethod]
getMethodsTermTypeErrors cls@(NewClazz2 _ _ nm _ _ methods) = do
  typeData <- lift get
  mapM (getMethodTermTypeErrors cls) methods

getMethodTermTypeErrors :: Clazz2 -> Method -> ExceptT [TypeError] (StateT ClassData IO) TypedMethod
getMethodTermTypeErrors cls method@(NewMethod pos nm params tp _ (MethodImpl t)) = do
  typeData <- lift get
  let methodEnvironment = createMethodEnvironment typeData cls method
  typedTerm <- runReaderT (getType t) methodEnvironment
  if tp == fst (TI.getBoxedType (getTypedTermType typedTerm))
    then return $ NewTypedMethod nm params tp (TypedMethodImpl typedTerm);
    else throwE [TypeError ("Incorrect return type: "++show (getTypedTermType typedTerm)) (SourcePos' pos)]
getMethodTermTypeErrors cls@(NewClazz2 _ _ _ extends _ _) method@(NewMethod pos nm params tp _ (ConstructorImpl maybeConstructorInvocation assignments)) = do
  typeData <- lift get
  let constructorRightEnvironment = createConstructorEnvironmentRight typeData cls method
  let constructorLeftEnvironment = createConstructorEnvironmentLeft typeData cls
  maybeEitherTypedConstructorInvocation <- case maybeConstructorInvocation of
    Just ci -> case ci of
      Left thisCI -> do
        typedCI <- runReaderT (getTypedConstructorInvocation cls thisCI) constructorRightEnvironment
        return $ Just (Left typedCI)
      Right superCI -> do
        typedCI <- runReaderT (getTypedSuperConstructorInvocation cls superCI) constructorRightEnvironment
        return $ Just (Right typedCI)
    Nothing -> return Nothing
  typedAssignments <- mapM (getAssignmentTypeError constructorLeftEnvironment constructorRightEnvironment) assignments
  case maybeEitherTypedConstructorInvocation of
    Just eitherTypedCI -> case eitherTypedCI of  
      Left typedThisCI -> 
        return $ NewTypedMethod P.createNameInit params P.createQNameObject (TypedConstructorImpl typedThisCI typedAssignments)
      Right typedSuperCI ->
        return $ NewTypedMethod P.createNameInit params P.createQNameObject (TypedConstructorImpl typedSuperCI typedAssignments)
    Nothing ->
      return $ case extends of
        NewExtends _ qn -> NewTypedMethod
          P.createNameInit
          params
          P.createQNameObject
          (TypedConstructorImpl (defaultConstructorInvocation qn)  typedAssignments)
        ExtendsObject -> NewTypedMethod
          P.createNameInit
          params
          P.createQNameObject
          (TypedConstructorImpl (defaultConstructorInvocation P.createQNameObject)  typedAssignments)

defaultConstructorInvocation :: P.QualifiedName -> TypedConstructorInvocation
defaultConstructorInvocation parentCls = NewTypedConstructorInvocation parentCls [] []

getAssignmentTypeError :: Environment -> Environment -> Assignment -> ExceptT [TypeError] (StateT ClassData IO) TypedAssignment
getAssignmentTypeError lenv renv (NewAssignment lpos leftTerm rpos rightTerm) = do
  typeData <- lift get
  leftTermType <- runReaderT (getType leftTerm) lenv
  rightTermType <- runReaderT (getType rightTerm) renv
  rti <- TI.getClassTypeInfoE (TI.getBoxedType (getTypedTermType rightTermType))
  lti <- TI.getClassTypeInfoE (TI.getBoxedType (getTypedTermType leftTermType))
  isSubtype <- TI.isSubtypeOfE (TI.getTypeName rti) (TI.getTypeName lti)
  if isTermValidForLeftAssignment leftTerm && isSubtype
    then return $ NewTypedAssignment leftTermType rightTermType
    else throwE [TypeError "Illegal assignment" (SourcePos' rpos)]

isTermValidForLeftAssignment :: Term -> Bool
isTermValidForLeftAssignment (Application (Value (Variable _ target)) (FieldAccess _ _)) = P.createNameThis == target
isTermValidForLeftAssignment (Application t (FieldAccess _ _)) = isTermValidForLeftAssignment t
isTermValidForLeftAssignment t = False

getTypedConstructorInvocation ::  Clazz2 -> ConstructorInvocation -> ReaderT Environment (ExceptT [TypeError] (StateT ClassData IO)) TypedConstructorInvocation
getTypedConstructorInvocation  cls@(NewClazz2 cpos _ tp extends _ _) (NewConstructorInvocation pos terms) = do
  constructorSuperInvocationEnvironment <- ask
  typedTerms <- mapM getType terms
  let signature = TI.ClassPathSignature init' (fmap getTypedTermType typedTerms)
  typeInfo <- lift $ TI.getClassTypeInfoE (tp,SourcePos' cpos)
  maybeThisConstructor <- lift $ getMethodType signature typeInfo
  case maybeThisConstructor of
    Nothing -> lift $ throwE [TypeError ("No invocation compatible constructor: "++show tp++"."++show signature) (SourcePos' pos)]
    Just (TI.NewMethodInvocation _ (TI.ClassPathSignature _ targetTermTypes)) ->
      return $ NewTypedConstructorInvocation tp targetTermTypes typedTerms

getTypedSuperConstructorInvocation ::  Clazz2 -> SuperConstructorInvocation -> ReaderT Environment (ExceptT [TypeError] (StateT ClassData IO)) TypedConstructorInvocation
getTypedSuperConstructorInvocation  cls@(NewClazz2 _ _ tp extends _ _) (NewSuperConstructorInvocation pos terms) = do
  constructorSuperInvocationEnvironment <- ask
  typedTerms <- mapM getType terms
  let signature = TI.ClassPathSignature init' (fmap getTypedTermType typedTerms)
  case extends of
    (NewExtends ppos parentClass) -> do
      parentTypeInfo <- lift $ TI.getClassTypeInfoE (parentClass,SourcePos' ppos)
      maybeSuperConstructor <- lift $ getMethodType signature parentTypeInfo
      case maybeSuperConstructor of
        Nothing -> lift $ throwE [TypeError ("No invocation compatible constructor: "++show tp++"."++show signature) (SourcePos' pos)]
        Just (TI.NewMethodInvocation _ (TI.ClassPathSignature _ targetTermTypes)) ->
          return $ NewTypedConstructorInvocation parentClass targetTermTypes typedTerms
    ExtendsObject -> return $ NewTypedConstructorInvocation P.createQNameObject [] []

getConstructorsUnassignedFieldErrors :: Clazz2 -> StateT ClassData IO [TypeError]
getConstructorsUnassignedFieldErrors cls@(NewClazz2 _ _ nm _ _ methods) = do
  let constructors = filter (\(NewMethod _ nm _ _ _ _) -> nm == P.createNameInit)  methods
  return $ foldr (\c list -> getConstructorUnassignedFieldError cls c ++ list) [] constructors

getConstructorUnassignedFieldError :: Clazz2 -> Method -> [TypeError]
getConstructorUnassignedFieldError cls@(NewClazz2 _ _ clsNm _ fields _) constructor@(NewMethod pos _ _ _ signature (ConstructorImpl _ assignments)) =
  let fieldSet = Set.fromList (fmap (\(NewField _ _ _ nm) -> nm) fields)
      assignedFieldSet = Set.fromList (mapMaybe (\(NewAssignment _ term _ _) -> getAssignmentTermField term) assignments)
      unassignedFieldSet = Set.difference fieldSet assignedFieldSet
  in
      [TypeError ("Constructor does not assign values to all fields: "++show signature) (SourcePos' pos) | Set.size unassignedFieldSet /= 0]

getAssignmentTermField :: Term -> Maybe P.SimpleName
getAssignmentTermField (Application (Value (Variable _ target)) (FieldAccess _ fieldName)) = if target == P.createNameThis then Just fieldName else Nothing
getAssignmentTermField (Application innerApplication@(Application _ _) _) = getAssignmentTermField innerApplication
getAssignmentTermField _ = Nothing

leastUpperBound :: [P.QualifiedName] -> ExceptT [TypeError] (StateT ClassData IO) TI.Type
leastUpperBound typeList = do
  st <- mapM TI.getSupertypeSet typeList
  let ec = List.nub (List.foldl' List.intersect [] st)
  maybeLub <-foldM (\mec tp -> case mec of
                            Nothing -> return $ Just tp
                            Just tp' -> ifM (TI.isSubtypeOfE (tp,CompiledCode) (tp',CompiledCode)) (return (Just tp)) (return (Just tp')))
    Nothing
    ec
  case maybeLub of
    Nothing -> return $ TI.L P.createQNameObject CompiledCode
    Just lub -> return $ TI.L lub CompiledCode