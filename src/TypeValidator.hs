{-# LANGUAGE RecordWildCards #-}

{-- 
TypeValidator converts Clazz2 values into ValidTypeClazz values by checking that all types referenced
in the Clazz2 values exist in compilation units being compiled or in the class path. The main function
tranformToValidTypes returns a list of TypeErrors is any undefined types are referenced in any of the 
compilation units, or a list of ValidTypeClazz values 

A ValidTypeClazz uses only ValidTypeNames and therefore, ValidTypeClazzes can be further typechecked 
without worrying about types being undefined, so methods to retrieve type data given a ValidTypeName are
never partial. 
-}

module TypeValidator (
  ClassData
, ValidTypeName(ClassPathVTN) -- No LocalVTN contructor exported for this type by design.
, ValidTypeAbstraction(..)
, ValidTypeTypeName(..)
, ValidTypeValue(..)
, ValidTypeApplicationTarget(..)
, ValidTypeTerm(..)
, ValidTypeParameter(..)
, ValidTypeConstructorInvocation(..)
, ValidTypeSuperConstructorInvocation(..)
, ValidTypeAssignment(..)
, ValidTypeMethodImplementation(..)
, ValidTypeField(..)
, ValidTypeMethod(..)
, ValidTypeClazz(..)
, ValidTypeClassData
, transformToValidTypes
, TypeValidator.createValidTypeNameObject
, TypeValidator.createValidTypeNameInteger
, TypeValidator.createValidTypeNameBoolean
, TypeValidator.createValidTypeNameString
, getValidTypeNameClassPath
, getClassPathValidTypeName
, isClassPathValidTypeName
) where

import Control.Monad.Trans.State.Strict (StateT,get,put,evalStateT,runStateT)
import Control.Monad.Trans.Class (lift)
import Text.Parsec (SourcePos)
import qualified Data.Validation as V
import Data.Int (Int32)
import qualified Data.Map.Strict as Map
import Control.Monad (foldM)
import TextShow (showb,toText)

import TypeCheckerTypes
import ClassPath (ClassPath,ClassPathValidTypeName,ClassDescriptor(..),hasClass,createValidTypeNameObject,createValidTypeNameBoolean,createValidTypeNameInteger,createValidTypeNameString,getClassValidTypeName)
import Parser2

type ClassData = (ClassPath,LocalClasses)

data ValidTypeName = LocalVTN QualifiedName | ClassPathVTN ClassPathValidTypeName deriving (Eq,Ord)

instance ValidTypeQName ValidTypeName where
  getValidTypeQName (LocalVTN qn) = qn
  getValidTypeQName (ClassPathVTN cpvtn) = getValidTypeQName cpvtn

data ValidTypeAbstraction = ValidTypeFieldAccess SourcePos SimpleName
                          | ValidTypeMethodInvocation SourcePos SimpleName [ValidTypeTerm]
                          | ValidTypeSuperMethodInvocation SourcePos SimpleName [ValidTypeTerm]
                          deriving Show

data ValidTypeTypeName = ValidTypeTypeName SourcePos ValidTypeName deriving Show

data ValidTypeValue = ValidTypeVariable SourcePos SimpleName
                    | ValidTypeIntegerLit SourcePos Int32
                    | ValidTypeStringLit SourcePos String
                    | ValidTypeBooleanLit SourcePos Bool
                    | ValidTypeObjectCreation SourcePos ValidTypeName [ValidTypeTerm]
                    deriving Show

data ValidTypeApplicationTarget = ValidTypeApplicationTargetTerm ValidTypeTerm
                                | ValidTypeApplicationTargetTypeName ValidTypeTypeName
                                deriving Show

data ValidTypeTerm = ValidTypeValue ValidTypeValue
                   | ValidTypeApplication ValidTypeApplicationTarget ValidTypeAbstraction
                   | ValidTypeConditional ValidTypeTerm ValidTypeTerm ValidTypeTerm
                   | ValidTypeCast ValidTypeTypeName ValidTypeTerm
                   deriving Show

data ValidTypeParameter = ValidTypeParameter { vpName :: (SimpleName, SourcePos)
                                             , vpType :: ValidTypeName
                                             } deriving (Show,Eq)

data ValidTypeConstructorInvocation = ValidTypeConstructorInvocation SourcePos [ValidTypeTerm] deriving Show

data ValidTypeSuperConstructorInvocation = ValidTypeSuperConstructorInvocation SourcePos [ValidTypeTerm] deriving Show

data ValidTypeAssignment = ValidTypeAssignment { vaRightHandTerm :: ValidTypeTerm
                                               , vaLeftHandTerm :: ValidTypeTerm
                                               } deriving Show

data ValidTypeMethodImplementation = ValidTypeMethodImplementation { vmiTerm :: ValidTypeTerm}
                                   | ValidTypeConstructorImplementation { vmiConstructorInvocation :: Either ValidTypeConstructorInvocation ValidTypeSuperConstructorInvocation
                                                                        , vmiAssignments :: [ValidTypeAssignment]
                                                                        } deriving Show

data ValidTypeField = ValidTypeField { vfName :: (SimpleName, SourcePos)
                                     , vfType :: ValidTypeName
                                     } deriving Show

data ValidTypeMethod = ValidTypeMethod { vmName :: (SimpleName, SourcePos)
                                       , vmAccessFlags :: [MethodAccessFlag ]
                                       , vmType :: ValidTypeName
                                       , vmParams :: [ValidTypeParameter]
                                       , vmMaybeImpl :: Maybe ValidTypeMethodImplementation
                                       } deriving Show

data ValidTypeClazz = ValidTypeClazz { vcAccessFlags :: [ClassAccessFlag]
                                     , vcName :: ValidTypeName
                                     , vcSourcePos :: SourcePos
                                     , vcParent :: (ValidTypeName, SourcePos)
                                     , vcFields :: [ValidTypeField]
                                     , vcMethods :: [ValidTypeMethod]
                                     } deriving Show

instance Show ValidTypeName where
  show (LocalVTN qn) = show qn
  show (ClassPathVTN cpvtn) = show cpvtn

type ValidTypeClassData = (ClassPath,Map.Map ValidTypeName ValidTypeClazz)

getValidTypeNameClassPath :: ClassPathValidTypeName -> ValidTypeName
getValidTypeNameClassPath = ClassPathVTN

getClassPathValidTypeName :: ValidTypeName -> ClassPathValidTypeName
getClassPathValidTypeName (LocalVTN _) = undefined
getClassPathValidTypeName (ClassPathVTN cpvtn) = cpvtn

isClassPathValidTypeName :: ValidTypeName -> Bool
isClassPathValidTypeName (LocalVTN _) = False
isClassPathValidTypeName (ClassPathVTN _) = True

createValidTypeNameObject = ClassPathVTN ClassPath.createValidTypeNameObject

createValidTypeNameInteger = ClassPathVTN ClassPath.createValidTypeNameInteger

createValidTypeNameBoolean = ClassPathVTN ClassPath.createValidTypeNameBoolean

createValidTypeNameString = ClassPathVTN ClassPath.createValidTypeNameString

transformToValidTypes :: StateT ClassData IO (Either [TypeError] [ValidTypeClazz])
transformToValidTypes = do
  (_,classMap) <- get
  V.toEither <$> foldM (\validate clazz -> do
    validTypeClassV <- getValidTypeClass clazz
    return $ (:) <$> validTypeClassV <*> validate) (V.Success []) (Map.elems classMap)

getValidTypeClass :: Clazz2 -> StateT ClassData IO (V.Validation [TypeError] ValidTypeClazz)
getValidTypeClass cls@(NewClazz2 pos _ vcAccessFlags nm _ _ _) = do
  let vcName = nm
  validTypeParentV <- V.fromEither <$> getClassParentValidType cls
  validTypeFieldsV <- getValidTypeFields cls
  validTypeMethodsV <- V.fromEither <$> getValidTypeMethods cls
  return $ ValidTypeClazz vcAccessFlags (LocalVTN nm) pos <$> validTypeParentV <*> validTypeFieldsV <*> validTypeMethodsV

getClassParentValidType :: Clazz2 -> StateT ClassData IO (Either [TypeError] (ValidTypeName, SourcePos))
getClassParentValidType (NewClazz2 pos _ _ _ ExtendsObject _ _) = return $ Right (TypeValidator.createValidTypeNameObject, pos)
getClassParentValidType (NewClazz2 _ _ _ _ (NewExtends pos parent) _ _) = do
  cond <- getValidTypeName parent
  case cond of
    Just vtn -> return $ Right (vtn, pos)
    Nothing -> return $ Left [TypeError ("Undefined type: "++show parent) pos]

getValidTypeFields :: Clazz2 -> StateT ClassData IO (V.Validation [TypeError] [ValidTypeField])
getValidTypeFields (NewClazz2 _ _ _ _ _ fields _) = do
  foldM (\fieldList field@(NewField pos tp npos nm) ->
    do
      cond <- getValidTypeName tp
      let validTypeFieldV =
            case cond of
              Just vtn -> V.Success (ValidTypeField{vfName=(nm,npos), vfType=vtn})
              Nothing -> V.Failure [TypeError ("Undefined type: "++show tp) pos]
      return $ (:) <$> validTypeFieldV <*> fieldList
    ) (V.Success []) fields

consEither :: Either [a] b -> Either [a] [b] -> Either [a] [b]
consEither head list =
  case list of
    Left xs -> case head of
      Left x -> Left (x++xs)
      Right _ -> Left xs
    Right xs -> case head of
      Right x -> Right (x:xs)
      Left x -> Left x

getValidTypeMethods :: Clazz2 -> StateT ClassData IO (Either [TypeError] [ValidTypeMethod])
getValidTypeMethods (NewClazz2 _ _ _ _ _ _ methods) =
  foldM (\either method -> do
    validTypeMethodE <- getValidTypeMethod method
    return $ consEither validTypeMethodE either)
  (Right [])
  methods

getValidTypeMethod :: Method -> StateT ClassData IO (Either [TypeError] ValidTypeMethod)
getValidTypeMethod method@(NewMethod pos vmAccessFlags nm params _ _ _) = do
  returnValidTypeV <- V.fromEither <$> getMethodReturnValidType method
  validTypeParamsV <- V.fromEither <$> getValidTypeParams params
  validTypeExpressionV <- V.fromEither <$> getMethodValidTypeExpression method
  return $ V.toEither (ValidTypeMethod (nm,pos) vmAccessFlags <$> returnValidTypeV <*> validTypeParamsV <*> validTypeExpressionV)

getMethodReturnValidType :: Method -> StateT ClassData IO (Either [TypeError] ValidTypeName)
getMethodReturnValidType (NewMethod pos _ _ _ tp _ _) = do
  cond <- getValidTypeName tp
  return $ case cond of 
    Just vtn -> Right vtn 
    Nothing -> Left [TypeError ("Undefined type: "++show tp) pos]

getValidTypeParams :: [Parameter] -> StateT ClassData IO (Either [TypeError] [ValidTypeParameter])
getValidTypeParams = fmap (fmap reverse) <$> foldM (\either (NewParameter pos tp nmpos nm) ->
    do
      cond <- getValidTypeName tp
      case either of
        Left typeErrors -> return $ Left (case cond of Nothing -> TypeError ("Undefined type: "++show tp) pos:typeErrors; Just _ -> typeErrors)
        Right typeList -> case cond of
          Just vtn -> return $ Right (ValidTypeParameter {vpName=(nm,nmpos), vpType=vtn}:typeList)
          Nothing -> return $ Left [TypeError ("Undefined type: "++show tp) pos]) (Right [])

getValidTypeArguments :: [Term] -> StateT ClassData IO (Either [TypeError] [ValidTypeTerm])
getValidTypeArguments = fmap (fmap reverse) <$> foldM (\either t ->
  do
    validTypeTermE <- getValidTypeTerm t
    return $ consEither validTypeTermE either) (Right [])

getMethodValidTypeExpression :: Method -> StateT ClassData IO (Either [TypeError] (Maybe ValidTypeMethodImplementation))
getMethodValidTypeExpression (NewMethod _ _ _ _ _ _ (Just (MethodImpl term))) = do
  validTypeTermE <- getValidTypeTerm term
  return $ case validTypeTermE of
    Right validTypeTerm -> Right (Just (ValidTypeMethodImplementation validTypeTerm))
    Left typeErrors -> Left typeErrors
getMethodValidTypeExpression (NewMethod _ _ _ _ _ _ (Just (ConstructorImpl (Left (NewConstructorInvocation pos args)) assignments))) = do
  validTypeAssignmentsE <- getValidTypeAssignments assignments
  validTypeArgsE <- getValidTypeArguments args
  return $ case validTypeArgsE of
    Right validTypeArgs -> case validTypeAssignmentsE of
      Right vmiAssignments -> Right (Just ValidTypeConstructorImplementation {..}) where
        vmiConstructorInvocation = Left (ValidTypeConstructorInvocation pos validTypeArgs)
      Left assignmentErrors -> Left assignmentErrors
    Left argErrors -> case validTypeAssignmentsE of
      Right _ -> Left argErrors
      Left assignmentErrors -> Left (argErrors++assignmentErrors)
getMethodValidTypeExpression (NewMethod _ _ _ _ _ _ (Just (ConstructorImpl (Right (NewSuperConstructorInvocation pos args)) assignments))) = do
  validTypeAssignmentsE <- getValidTypeAssignments assignments
  validTypeArgsE <- getValidTypeArguments args
  return $ case validTypeArgsE of
    Right validTypeArgs -> case validTypeAssignmentsE of
      Right vmiAssignments -> Right (Just ValidTypeConstructorImplementation {..}) where
        vmiConstructorInvocation = Right (ValidTypeSuperConstructorInvocation pos validTypeArgs)
      Left assignmentErrors -> Left assignmentErrors
    Left argErrors -> case validTypeAssignmentsE of
      Right _ -> Left argErrors
      Left assignmentErrors -> Left (argErrors++assignmentErrors)
getMethodValidTypeExpression (NewMethod _ _ _ _ _ _ Nothing) =
  return $ Right Nothing

getValidTypeAssignments :: [Assignment]-> StateT ClassData IO (Either [TypeError] [ValidTypeAssignment])
getValidTypeAssignments = fmap (fmap reverse) <$> foldM (\either a -> do
  validTypeAssignmentE <- getValidTypeAssignment a
  return $ consEither validTypeAssignmentE either)
  (Right [])

getValidTypeAssignment :: Assignment -> StateT ClassData IO (Either [TypeError] ValidTypeAssignment)
getValidTypeAssignment (NewAssignment lpos t1 rpos t2) = do
  lhTermE <- getValidTypeTerm t1
  rhTermE <- getValidTypeTerm t2
  case lhTermE of
    Left lherrors -> case rhTermE of
      Left rherrors -> return $ Left (rherrors++lherrors)
      Right _ -> return $ Left lherrors
    Right vaLeftHandTerm -> case rhTermE of
      Left rherrors -> return $ Left rherrors
      Right vaRightHandTerm -> return $ Right (ValidTypeAssignment {..})

getValidTypeTerm :: Term -> StateT ClassData IO (Either [TypeError] ValidTypeTerm)
getValidTypeTerm (Value (ObjectCreation pos (TypeName tppos tp) args)) = do
  cond <- getValidTypeName tp
  validTypeArgumentsE <- getValidTypeArguments args
  case cond of 
    Nothing -> case validTypeArgumentsE of 
      Left errors -> return $ Left $ errors++[TypeError ("Undefined type: "++show tp) pos] 
      Right _ -> return $ Left [TypeError ("Undefined type: "++show tp) pos]
    Just vtn -> case validTypeArgumentsE of
      Left errors -> return $ Left errors
      Right validTypeArguments -> return $ Right (ValidTypeValue (ValidTypeObjectCreation pos vtn validTypeArguments))
getValidTypeTerm (Cast (TypeName pos tp) term) = do
  cond <- getValidTypeName tp
  validTypeTermE <- getValidTypeTerm term
  return $ case cond of
    Nothing -> case validTypeTermE of
      Left termTypeErrors -> Left $ termTypeErrors++[TypeError ("Undefined type: "++show tp) pos] 
      Right _ -> Left [TypeError ("Undefined type: "++show tp) pos]
    Just vtn -> case validTypeTermE of
      Left termTypeErrors -> Left termTypeErrors
      Right validTypeTerm -> Right (ValidTypeCast (ValidTypeTypeName pos vtn) validTypeTerm)
getValidTypeTerm (Application (ApplicationTargetTerm t) (FieldAccess pos nm)) = do
  validTypeTermE <- getValidTypeTerm t
  case validTypeTermE of
    Right validTypeTerm -> return $ Right (ValidTypeApplication (ValidTypeApplicationTargetTerm validTypeTerm)
                                                        (ValidTypeFieldAccess pos nm))
    Left termTypeErrors -> return $ Left termTypeErrors
getValidTypeTerm (Application (ApplicationTargetTerm t) (MethodInvocation pos nm params)) = do
  validTypeTermE <- getValidTypeTerm t
  validTypeParamsE <- fmap reverse <$> foldM (\either t'' -> do
    vtp <- getValidTypeTerm t''
    return $ consEither vtp either) (Right []) params
  case validTypeTermE of
    Right validTypeTerm -> case validTypeParamsE of
      Right validTypeParams -> return $ Right (ValidTypeApplication (ValidTypeApplicationTargetTerm validTypeTerm)
                                                            (ValidTypeMethodInvocation pos nm validTypeParams))
      Left paramTypeErrors -> return $ Left paramTypeErrors
    Left termTypeErrors -> case validTypeParamsE of
      Left paramTypeErrors -> return $ Left (paramTypeErrors++termTypeErrors)
      Right _ -> return $ Left termTypeErrors
getValidTypeTerm (Application (ApplicationTargetTerm t) (SuperMethodInvocation pos nm params)) = do
  validTypeTermE <- getValidTypeTerm t
  validTypeParamsE <- fmap reverse <$> foldM (\either t'' -> do
    vtp <- getValidTypeTerm t''
    return $ consEither vtp either) (Right []) params
  case validTypeTermE of
    Right validTypeTerm -> case validTypeParamsE of
      Right validTypeParams -> return $ Right (ValidTypeApplication (ValidTypeApplicationTargetTerm validTypeTerm)
                                                            (ValidTypeSuperMethodInvocation pos nm validTypeParams))
      Left paramTypeErrors -> return $ Left paramTypeErrors
    Left termTypeErrors -> case validTypeParamsE of
      Left paramTypeErrors -> return $ Left (paramTypeErrors++termTypeErrors)
      Right _ -> return $ Left termTypeErrors
getValidTypeTerm (Application (ApplicationTargetTypeName (TypeName tppos tp)) (FieldAccess pos nm)) = do
  cond <- getValidTypeName tp
  case cond of
    Just vtn -> return $ Right (ValidTypeApplication
                           (ValidTypeApplicationTargetTypeName (ValidTypeTypeName tppos vtn))
                           (ValidTypeFieldAccess pos nm))
    Nothing -> return $ Left [TypeError ("Undefined type: "++show tp) tppos]
getValidTypeTerm (Application (ApplicationTargetTypeName (TypeName tppos tp)) (MethodInvocation pos nm params)) = do
  cond <- getValidTypeName tp  
  validTypeParamsE <- fmap reverse <$> foldM (\either t'' -> do
      vtp <- getValidTypeTerm t''
      return $ consEither vtp either) (Right []) params
  return $ case cond of
    Nothing -> case validTypeParamsE of
      Left typeErrors -> Left $ typeErrors++[TypeError ("Undefined type: "++show tp) tppos]
      Right _ -> Left [TypeError ("Undefined type: "++show tp) tppos]
    Just vtn -> case validTypeParamsE of
      Right validTypeParams -> Right (ValidTypeApplication
                                                (ValidTypeApplicationTargetTypeName (ValidTypeTypeName tppos vtn))
                                                (ValidTypeMethodInvocation pos nm validTypeParams))
      Left typeErrors -> Left typeErrors
getValidTypeTerm (Application (ApplicationTargetTypeName (TypeName tppos tp)) (SuperMethodInvocation pos nm params)) = undefined
getValidTypeTerm (Value (Variable pos sn)) = return $ Right (ValidTypeValue (ValidTypeVariable pos sn))
getValidTypeTerm (Value (IntegerLit pos i)) = return $ Right (ValidTypeValue (ValidTypeIntegerLit pos i))
getValidTypeTerm (Value (StringLit pos s)) = return $ Right (ValidTypeValue (ValidTypeStringLit pos s))
getValidTypeTerm (Value (BooleanLit pos b)) = return $ Right (ValidTypeValue (ValidTypeBooleanLit pos b))
getValidTypeTerm (Conditional cond ifTerm elseTerm) = do
  V.toEither <$> getValidTypeConditional cond ifTerm elseTerm

getValidTypeConditional :: Term -> Term -> Term -> StateT ClassData IO (V.Validation [TypeError] ValidTypeTerm)
getValidTypeConditional cond ifTerm elseTerm = do
  condV <- V.fromEither <$> getValidTypeTerm cond
  ifTermV <- V.fromEither <$> getValidTypeTerm ifTerm
  elseTermV <- V.fromEither <$> getValidTypeTerm elseTerm
  return $ ValidTypeConditional <$> condV <*> ifTermV <*> elseTermV

getValidTypeName :: QualifiedName -> StateT ClassData IO (Maybe ValidTypeName)
getValidTypeName tp = do
  (classPath,classMap) <- get
  return $ if Map.member tp classMap
    then Just (LocalVTN tp)
    else do
      let maybeClassPathType = getClassValidTypeName classPath tp 
      case maybeClassPathType of
        Just cpvtn -> Just (ClassPathVTN cpvtn)
        Nothing -> Nothing 
