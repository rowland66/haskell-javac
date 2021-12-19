{-# LANGUAGE FlexibleContexts #-}

module TypeChecker
  ( typeCheck
  ,  TypeError
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
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Either as Either
import qualified Data.Maybe as Maybe
import Data.Word
import Parser2
import qualified Parser as P
import Environment
import Text.ParserCombinators.Parsec (SourcePos)
import Debug.Trace

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
  show (TypeError str pos) = str ++ "\nat: " ++ (show pos)

getTypedTermType :: TypedTerm -> P.QualifiedName
getTypedTermType (TypedValue (TypedVariable {vTyp=tp})) = tp
getTypedTermType (TypedValue (TypedObjectCreation {ocTyp=tp})) = tp
getTypedTermType (TypedValue (TypedCast {cTyp=tp})) = tp
getTypedTermType (TypedApplication _ (TypedFieldAccess {fTyp=tp})) = tp
getTypedTermType (TypedApplication _ (TypedMethodInvocation {mTyp=tp})) = tp

typeCheck :: (Map.Map P.QualifiedName Clazz2) -> Maybe [TypeError]
typeCheck classMap =
  let result = checkForDuplicateTypeErrors (Map.insert P.createQNameObject (NewClazz2 CompiledCode P.createQNameObject ExtendsObject [] [(NewConstructor CompiledCode [] (Signature P.createNameInit []) Nothing [])] []) classMap)
                 >>= checkForDeclaredTypeErrors
                 >>= checkForClassInheritenceCycles
                 >>= checkForConstructorsUnassignedFieldErrors in
  case result of
    Left errorList -> Just errorList
    Right _ -> Nothing

transform :: (Map.Map P.QualifiedName Clazz2) -> Either [TypeError] [TypedClazz]
transform classMap =
  let clazzList = foldr (\cls list -> (runReader (getTypedClazz cls) (Map.insert P.createQNameObject (NewClazz2 CompiledCode P.createQNameObject ExtendsObject [] [(NewConstructor CompiledCode [] (Signature P.createNameInit []) Nothing [])] []) classMap)):list) [] classMap
      (typeErrors, typedClazzs) = Either.partitionEithers clazzList in
  if (not (null typeErrors)) then Left (concat typeErrors) else Right (typedClazzs)

checkForDuplicateTypeErrors :: (Map.Map P.QualifiedName Clazz2) -> (Either [TypeError] (Map.Map P.QualifiedName Clazz2))
checkForDuplicateTypeErrors classMap = do
  let errors = foldr (\cls list -> (getDuplicateFields cls) ++ (getDuplicateMethods cls) ++ list) ([] :: [TypeError]) classMap
  case (errors) of
    [] -> Right classMap
    _ -> Left errors

checkForDeclaredTypeErrors :: (Map.Map P.QualifiedName Clazz2) -> (Either [TypeError] (Map.Map P.QualifiedName Clazz2))
checkForDeclaredTypeErrors classMap = do
  let errors = foldr (\cls list -> (runReader (getClassDeclaredTypeErrors cls) classMap) ++
                                   (runReader (getConstructorsDeclaredTypeErrors cls) classMap) ++
                                   (runReader (getFieldDeclaredTypeErrors cls) classMap) ++
                                   (runReader (getMethodsDeclaredTypeErrors cls) classMap) ++ list) [] classMap
  trace "checkForDeclaredTypeErrors" $ case (errors) of
    [] -> Right classMap
    _ -> Left errors

checkForClassInheritenceCycles :: (Map.Map P.QualifiedName Clazz2) -> (Either [TypeError] (Map.Map P.QualifiedName Clazz2))
checkForClassInheritenceCycles classMap = trace "checkForClassInheritenceCycles" $ checkForErrors classMap getClassInheritenceCycleErrors

checkForConstructorsUnassignedFieldErrors :: (Map.Map P.QualifiedName Clazz2) -> (Either [TypeError] (Map.Map P.QualifiedName Clazz2))
checkForConstructorsUnassignedFieldErrors classMap = trace "checkForConstructorsUnassignedFieldErrors" $ checkForErrors classMap getConstructorsUnassignedFieldErrors

checkForErrors :: (Map.Map P.QualifiedName Clazz2) -> (Clazz2 -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]) -> (Either [TypeError] (Map.Map P.QualifiedName Clazz2))
checkForErrors classMap getErrorsFunction = do
  let errors = foldr (\cls list -> (runReader (getErrorsFunction cls) classMap) ++ list) [] classMap
  case (errors) of
    [] -> Right classMap
    _ -> Left errors

getType :: Term -> Reader (Environment, Map.Map P.QualifiedName Clazz2) (Either [TypeError] TypedTerm)
getType (Value (Variable pos x)) = do
  (env, classMap) <- ask
  return $ case (env !? x) of Just (tp,ndx) -> (Right (TypedValue (TypedVariable {vPosition=(fromIntegral ndx :: Word8),vTyp=tp}))); Nothing -> (Left [(TypeError ("Undefined variable: "++(show x)) pos)])
getType (Value (ObjectCreation pos tp params)) = do
  (env, classMap) <- ask
  let createClass = (classMap Map.! tp)
  eitherParamTypes <- sequence (fmap getType params)
  if (null (Either.lefts eitherParamTypes)) then do
    let paramTerms = (Either.rights eitherParamTypes)
    let signature = (Signature P.createNameInit (fmap getTypedTermType paramTerms))
    let constructorExists = (hasConstructorWithSignature signature createClass classMap)
    if constructorExists then
      return (Right (TypedValue (TypedObjectCreation {ocTyp=tp, ocTerms=paramTerms})))
    else
      (return (Left [(TypeError ("Undefined constructor: "++(show tp)++"."++(show signature)) pos)]))
  else return $ Left (concat (Either.lefts eitherParamTypes))
getType (Value (Cast pos tp t)) = do
  (env, classMap) <- ask
  eitherTypedTerm <- getType t
  let castClass = (classMap Map.! tp)
  case eitherTypedTerm of
    Right typedTerm ->
      return $ if (isSubtypeOf classMap castClass (classMap Map.! (getTypedTermType typedTerm)))
               then (Right (TypedValue (TypedCast {cTyp=tp, cTerm=typedTerm})))
               else (Left [(TypeError ("Invalid cast: "++(show tp)) pos)])
    Left e -> return $ Left e
getType (Application t (FieldAccess pos nm)) = do
  (env, classMap) <- ask
  eitherTypedTerm <- getType t
  case eitherTypedTerm of
    Right tt -> liftM (\mft -> case mft of Just tp -> (Right (TypedApplication tt (TypedFieldAccess {fName=nm,fTyp=tp}))); Nothing -> (Left [(TypeError ("Undefined field: "++(show nm)) pos)])) (getFieldType nm (classMap Map.! (getTypedTermType tt)))
    Left e -> return $ Left e
getType (Application t (MethodInvocation pos nm params)) = do
  (env, classMap) <- ask
  eitherTypedTerm <- getType t
  eitherParamTypes <- sequence (fmap getType params)
  if (null (Either.lefts eitherParamTypes)) then do
    let paramTypedTerms = (Either.rights eitherParamTypes)
    let signature = (Signature nm (fmap getTypedTermType paramTypedTerms))
    case eitherTypedTerm of
      Right tt -> do
        maybeMethodDataType <- (getMethodType signature (classMap Map.! (getTypedTermType tt)))
        case maybeMethodDataType of
          Just tp -> return (Right (TypedApplication tt (TypedMethodInvocation {mName=nm,mTyp=tp,mTerms=paramTypedTerms})))
          Nothing -> return (Left [(TypeError ("Undefined method: "++(show signature)) pos)])
      Left e -> return (Left e)
  else return $ Left (concat (Either.lefts eitherParamTypes))

infix 4 `isSubtypeOf`

isSubtypeOf :: (Map.Map P.QualifiedName Clazz2) -> Clazz2 -> Clazz2 -> Bool
isSubtypeOf classMap (NewClazz2 _ nm (ExtendsObject) _ _ _) parent@(NewClazz2 _ parentName _ _ _ _) =
  if (nm == parentName) || (P.createQNameObject == parentName) then True else False
isSubtypeOf classMap (NewClazz2 _ nm (NewExtends pos clsParent) _ _ _) parent@(NewClazz2 _ parentName _ _ _ _) =
  if (nm == parentName) || (clsParent == parentName) then True else (isSubtypeOf classMap (classMap Map.! clsParent) parent)

getFieldType :: P.SimpleName -> Clazz2 -> Reader (Environment, Map.Map P.QualifiedName Clazz2) (Maybe P.QualifiedName)
getFieldType nm (NewClazz2 _ _ extends fields _ _) = do
  (_, classMap) <- ask
  let field = List.find (\(NewField _ _ _ fieldNm) -> (nm == fieldNm)) fields
  case field of
    Just _ -> return $ fmap (\(NewField _ tp _ _) -> tp) field
    Nothing -> case extends of ExtendsObject -> return Nothing; (NewExtends _ parent) -> (getFieldType nm (classMap Map.! parent))

getMethodType :: Signature -> Clazz2 -> Reader (Environment, Map.Map P.QualifiedName Clazz2) (Maybe P.QualifiedName)
getMethodType signature (NewClazz2 _ _ extends _ _ methods) = do
  (_, classMap) <- ask
  let maybeMethod = List.find (\(NewMethod _ _ _ _ sig _) -> sig == signature) methods
  case maybeMethod of
    Just _ -> return $ fmap (\(NewMethod _ _ _ tp _ _ ) -> tp) maybeMethod
    Nothing -> case extends of ExtendsObject -> return Nothing; (NewExtends _ parent) -> (getMethodType signature (classMap Map.! parent))

hasConstructorWithSignature :: Signature -> Clazz2 -> (Map.Map P.QualifiedName Clazz2) -> Bool
hasConstructorWithSignature signature (NewClazz2 _ _ _ _ constructors _) classMap =
  let maybeConstructor = List.find (\(NewConstructor _ _ sig _ _) -> isCompatible signature sig classMap) constructors in
  case maybeConstructor of
    Just _ -> True
    Nothing -> False

isCompatible :: Signature -> Signature -> (Map.Map P.QualifiedName Clazz2) -> Bool
isCompatible sig1@(Signature nm1 types1) sig2@(Signature nm2 types2) classMap =
  if (nm1 /= nm2) then False else
    if ((length types1) /= (length types2)) then False else
      let classPairs = fmap (\(t1,t2) -> ((classMap Map.! t1),(classMap Map.! t2))) (zip types1 types2) in
      foldr (\(c1,c2) result -> if (result && (isSubtypeOf classMap c1 c2)) then True else False) True classPairs

getDuplicateFields :: Clazz2 -> [TypeError]
getDuplicateFields (NewClazz2 _ _ _ fields _ _) =
  snd $ foldr (\field@(NewField pos tp _ nm) (fieldMap, duplicateList) ->
    (case (Map.lookup nm fieldMap) of
      Nothing -> ((Map.insert nm nm fieldMap), duplicateList)
      Just _ -> (fieldMap, (TypeError ("Duplicate field: "++(show nm)) pos):duplicateList)))
    (Map.empty, [])
    fields

getDuplicateMethods :: Clazz2 -> [TypeError]
getDuplicateMethods (NewClazz2 _ _ _ _ _ methods) =
  snd $ foldr (\method@(NewMethod pos _ _ _ sig@(Signature nm params) _) (methodMap, duplicateList) ->
    (case (Map.lookup nm methodMap) of
      Nothing -> ((Map.insert nm [params] methodMap), duplicateList)
      Just paramsList -> if (List.elem params paramsList)
        then (methodMap, (TypeError ("Duplicate method: "++(show sig)) pos):duplicateList)
        else ((Map.update (\l -> (Just (params:l))) nm methodMap), duplicateList)))
    (Map.empty, [])
    methods

isValidClass :: P.QualifiedName -> (Map.Map P.QualifiedName Clazz2) -> Bool
isValidClass tp classMap = (tp == P.createQNameObject || Map.member tp classMap)

getClassDeclaredTypeErrors :: Clazz2 -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getClassDeclaredTypeErrors (NewClazz2 _ _ ExtendsObject _ _ _) = return []
getClassDeclaredTypeErrors (NewClazz2 _ _ (NewExtends pos parent) _ _ _) = do
  classMap <- ask
  return $ if (isValidClass parent classMap) then [] else [(TypeError ("Undefined type: "++(show parent)) pos)]

getFieldDeclaredTypeErrors :: Clazz2 -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getFieldDeclaredTypeErrors (NewClazz2 _ _ _ fields _ _) = do
  classMap <- ask
  return $ foldr (\field@(NewField pos tp _ _) errorList ->
    (if (isValidClass tp classMap) then errorList else (TypeError ("Undefined type: "++(show tp)) pos):errorList))
    []
    fields

getMethodsDeclaredTypeErrors :: Clazz2 -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getMethodsDeclaredTypeErrors (NewClazz2 _ _ _ _ _ methods) = do
  classMap <- ask
  foldM (\errorList method -> (fmap (\l -> l ++ errorList) (getMethodDeclaredTypeErrors method))) [] methods

getMethodDeclaredTypeErrors :: Method -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getMethodDeclaredTypeErrors method = do
  returnDeclaredTypeErrors <- getMethodReturnDeclaredTypeErrors method
  paramDeclaredTypeErrors <- getMethodParamDeclaredTypeErrors method
  expressionDeclaredTypeErrors <- getMethodExpressionDeclaredTypeErrors method
  return $ returnDeclaredTypeErrors ++ paramDeclaredTypeErrors ++ expressionDeclaredTypeErrors

getMethodReturnDeclaredTypeErrors :: Method -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getMethodReturnDeclaredTypeErrors (NewMethod pos _ _ tp _ _) = do
  classMap <- ask
  return $ if (isValidClass tp classMap) then [] else [(TypeError ("Undefined type: "++(show tp)) pos)]

getMethodParamDeclaredTypeErrors :: Method -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getMethodParamDeclaredTypeErrors (NewMethod _ _ params _ _ _) = do
  classMap <- ask
  getParamDeclaredTypeErrors params

getMethodExpressionDeclaredTypeErrors :: Method -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getMethodExpressionDeclaredTypeErrors (NewMethod _ _ _ _ _ term) = do
  classMap <- ask
  getTermDeclaredTypeErrors term

getConstructorsDeclaredTypeErrors :: Clazz2 -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getConstructorsDeclaredTypeErrors (NewClazz2 _ _ _ _ constructors _) = do
  classMap <- ask
  foldM (\errorList (NewConstructor _ _ _ _ assignments) -> (fmap (\l -> l ++ errorList) (getAssignmentsDeclaredTypeErrors assignments))) [] constructors

getConstructorDeclaredTypeErrors :: Constructor -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getConstructorDeclaredTypeErrors (NewConstructor _ params _ _ assignments) = do
  classMap <- ask
  paramDeclaredTypeErrors <- getParamDeclaredTypeErrors params
  assignmentDeclaredTypeErrors <- getAssignmentsDeclaredTypeErrors assignments
  return $ paramDeclaredTypeErrors ++ assignmentDeclaredTypeErrors

getParamDeclaredTypeErrors :: [Parameter] -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getParamDeclaredTypeErrors params = do
  classMap <- ask
  return $ foldr (\(NewParameter pos tp _) errorList -> (if (isValidClass tp classMap) then errorList else (TypeError ("Undefined type: "++(show tp)) pos):errorList)) [] params

getAssignmentsDeclaredTypeErrors :: [Assignment]-> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getAssignmentsDeclaredTypeErrors assignments = do
  classMap <- ask
  foldM (\errorList a -> (fmap (\l -> l ++ errorList) (getAssignmentDeclaredTypeErrors a))) [] assignments

getAssignmentDeclaredTypeErrors :: Assignment -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getAssignmentDeclaredTypeErrors (NewAssignment pos t1 t2) = do
  classMap <- ask
  t1errors <- getTermDeclaredTypeErrors t1
  t2errors <- getTermDeclaredTypeErrors t2
  return (t1errors ++ t2errors)

getTermDeclaredTypeErrors :: Term -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getTermDeclaredTypeErrors t = do
  classMap <- ask
  case t of
    (Value (Variable _ _)) -> return []
    (Value (ObjectCreation pos tp params)) -> liftM2 (++) paramErrors classError
      where
        classError = return (if (isValidClass tp classMap) then [] else [(TypeError ("Undefined type: "++(show tp)) pos)])
        paramErrors = foldM (\errs t' -> (fmap (\l -> l ++ errs) (getTermDeclaredTypeErrors t'))) [] params
    (Value (Cast pos tp term)) -> liftM2 (++) termError classError
      where
        classError = return (if (isValidClass tp classMap) then [] else [(TypeError ("Undefined type: "++(show tp)) pos)])
        termError = (getTermDeclaredTypeErrors term)
    (Application t' (FieldAccess _ _)) -> (getTermDeclaredTypeErrors t')
    (Application t' (MethodInvocation pos nm params)) ->  liftM2 (++) paramErrors termErrors
      where
        termErrors = (getTermDeclaredTypeErrors t')
        paramErrors = foldM (\errs t'' -> (fmap (\l -> l ++ errs) (getTermDeclaredTypeErrors t''))) [] params

getClassInheritenceCycleErrors :: Clazz2 -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getClassInheritenceCycleErrors clazz = getClassInheritenceCycleErrors' clazz []

getClassInheritenceCycleErrors' :: Clazz2 -> [P.QualifiedName] -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getClassInheritenceCycleErrors' (NewClazz2 _ _ ExtendsObject _ _ _) _ = return []
getClassInheritenceCycleErrors' (NewClazz2 _ nm (NewExtends pos parent) _ _ _) classes = do
  classMap <- trace ("start getClassInheritenceCycleErrors'"++(show nm)++":"++(show parent)) $ ask
  if (elem parent classes) then return ([(TypeError ("Cyclic Inheritence: "++(show nm)) pos)]) else (getClassInheritenceCycleErrors' (classMap Map.! parent) (parent : classes))

getTypedClazz :: Clazz2 -> (Reader (Map.Map P.QualifiedName Clazz2) (Either [TypeError] TypedClazz))
getTypedClazz cls@(NewClazz2 _ name extends fields _ _) = do
  eitherCorE <- getConstructorsTypeErrors cls
  eitherMorE <- getMethodsTermTypeErrors cls
  return $ case eitherCorE of
    Left constructorErrors -> case eitherMorE of Left methodErrors -> Left (constructorErrors ++ methodErrors); Right _ -> Left constructorErrors
    Right typedConstructors -> case eitherMorE of Left methodErrors -> Left methodErrors; Right typedMethods -> Right (NewTypedClazz name extends fields typedConstructors typedMethods)

getMethodsTermTypeErrors :: Clazz2 -> Reader (Map.Map P.QualifiedName Clazz2) (Either [TypeError] [TypedMethod])
getMethodsTermTypeErrors cls@(NewClazz2 _ nm _ _ _ methods) = do
  classMap <- ask
  let eitherList = foldr (\m list -> (getMethodTermTypeErrors cls m classMap):list) [] methods
  let (errorList, typedMethodList) = Either.partitionEithers eitherList
  return $ if (not (null errorList)) then Left (concat errorList) else Right typedMethodList

getMethodTermTypeErrors :: Clazz2 -> Method -> (Map.Map P.QualifiedName Clazz2) -> (Either [TypeError] TypedMethod)
getMethodTermTypeErrors cls method@(NewMethod pos nm params tp _ t) classMap =
  let methodEnvironment = (createMethodEnvironment classMap cls method) in
    case (runReader (getType t) (methodEnvironment, classMap)) of
      Right typedTerm -> if (tp == (getTypedTermType typedTerm)) then
                            (Right (NewTypedMethod nm params tp typedTerm));
                          else
                            (Left [(TypeError ("Incorrect return type: "++(show (getTypedTermType typedTerm))) pos)])
      Left e -> (Left e)

getConstructorsTypeErrors :: Clazz2 -> Reader (Map.Map P.QualifiedName Clazz2) (Either [TypeError] [TypedConstructor])
getConstructorsTypeErrors cls@(NewClazz2 _ nm _ _ constructors _) = do
  classMap <- ask
  let eitherList = foldr (\c list -> (getConstructorTypeErrors cls c classMap):list) [] constructors
  let (errorList,constructorList) = Either.partitionEithers eitherList
  return $ if (not (null errorList)) then Left (concat errorList) else Right constructorList

getConstructorTypeErrors :: Clazz2 -> Constructor -> (Map.Map P.QualifiedName Clazz2) -> (Either [TypeError] TypedConstructor)
getConstructorTypeErrors cls@(NewClazz2 _ clsNm _ _ _ _) constructor@(NewConstructor pos params _ maybeConstructorInvocation assignments) classMap =
  let constructorRightEnvironment = (createConstructorEnvironmentRight classMap cls constructor)
      constructorLeftEnvironment = (createConstructorEnvironmentLeft classMap cls)
      maybeEitherC = case maybeConstructorInvocation of Just ci -> Just (getConstructorSuperInvocationTypeErrors constructorRightEnvironment cls ci classMap); Nothing -> Nothing
      eitherList = foldr (\a list -> (getAssignmentTypeError constructorLeftEnvironment constructorRightEnvironment a classMap):list) [] assignments
      (assignmentTypeErrors,typedAssignments) = Either.partitionEithers eitherList in
      case maybeEitherC of
        Just eitherC ->
          case eitherC of
            Left le -> Left (le ++ (concat assignmentTypeErrors))
            Right ci -> if (not (null assignmentTypeErrors)) then Left (concat assignmentTypeErrors) else Right (NewTypedConstructor params ci typedAssignments)
        Nothing ->
          if (not (null assignmentTypeErrors)) then Left (concat assignmentTypeErrors) else Right (NewTypedConstructor params defaultConstructor typedAssignments)

defaultConstructor :: TypedConstructorInvocation
defaultConstructor = NewTypedConstructorInvocation []

getAssignmentTypeError :: Environment -> Environment -> Assignment -> (Map.Map P.QualifiedName Clazz2) -> (Either [TypeError] TypedAssignment)
getAssignmentTypeError lenv renv (NewAssignment pos leftTerm rightTerm) classMap =
  let leftTermType = (runReader (getType leftTerm) (lenv, classMap))
      rightTermType = (runReader (getType rightTerm) (renv, classMap)) in
    case leftTermType of
      Left le -> case rightTermType of Left re -> (Left (le++re)); Right _ -> Left le
      Right ltp ->
        case rightTermType of
          Left re -> Left re
          Right rtp -> if ((isTermValidForLeftAssignment leftTerm) &&
                           (isSubtypeOf classMap (classMap Map.! (getTypedTermType rtp)) (classMap Map.! (getTypedTermType ltp))))
                         then Right (NewTypedAssignment ltp rtp)
                         else (Left [(TypeError ("Illegal assignment") pos)])

isTermValidForLeftAssignment :: Term -> Bool
isTermValidForLeftAssignment (Application (Value (Variable _ target)) (FieldAccess _ _)) = if (P.createNameThis == target) then True else False
isTermValidForLeftAssignment (Application t (FieldAccess _ _)) = isTermValidForLeftAssignment t
isTermValidForLeftAssignment t = False

getConstructorSuperInvocationTypeErrors :: Environment -> Clazz2 -> ConstructorInvocation -> (Map.Map P.QualifiedName Clazz2) -> (Either [TypeError] TypedConstructorInvocation)
getConstructorSuperInvocationTypeErrors constructorSuperInvocationEnvironment cls@(NewClazz2 _ _ extends _ _ _) (NewConstructorInvocation pos terms) classMap =
  let eitherTermTypes = fmap (\t -> (runReader (getType t) (constructorSuperInvocationEnvironment,classMap))) terms in
      if (null (Either.lefts eitherTermTypes)) then
        let termTypes = (Either.rights eitherTermTypes)
            signature = (Signature P.createNameInit (fmap getTypedTermType termTypes)) in
            case extends of
              (NewExtends _ parentClass) -> if (hasConstructorWithSignature signature (classMap Map.! parentClass) classMap) then Right (NewTypedConstructorInvocation termTypes) else Left [(TypeError ("No constructor in "++(show parentClass)++" with signature "++(show signature)) pos)]
              (ExtendsObject) -> Right (NewTypedConstructorInvocation termTypes)
      else Left (concat (Either.lefts eitherTermTypes))

getConstructorsUnassignedFieldErrors :: Clazz2 -> Reader (Map.Map P.QualifiedName Clazz2) [TypeError]
getConstructorsUnassignedFieldErrors cls@(NewClazz2 _ nm _ _ constructors _) = do
  classMap <- trace "enter getConstructorsUnassignedFieldErrors" $ ask
  return $ foldr (\c list -> (getConstructorUnassignedFieldError cls c classMap) ++ list) [] constructors

getConstructorUnassignedFieldError :: Clazz2 -> Constructor -> (Map.Map P.QualifiedName Clazz2) -> [TypeError]
getConstructorUnassignedFieldError cls@(NewClazz2 _ clsNm _ fields _ _) constructor@(NewConstructor pos _ signature _ assignments) classMap =
  let fieldSet = Set.fromList (fmap (\(NewField _ _ _ nm) -> nm) fields)
      assignedFieldSet = Set.fromList (Maybe.catMaybes (fmap (\(NewAssignment _ term _) -> (getAssignmentTermField term)) assignments))
      unassignedFieldSet = (Set.difference fieldSet assignedFieldSet)
  in
      if ((Set.size unassignedFieldSet) == 0) then [] else (case pos of (SourcePos' pos) -> [(TypeError ("Constructor does not assign values to all fields: "++(show signature)) pos)]; (CompiledCode) -> [])

getAssignmentTermField :: Term -> Maybe P.SimpleName
getAssignmentTermField (Application (Value (Variable _ target)) (FieldAccess _ fieldName)) = if (target == P.createNameThis) then (Just fieldName) else Nothing
getAssignmentTermField (Application innerApplication@(Application _ _) _) = getAssignmentTermField innerApplication
getAssignmentTermField _ = Nothing
