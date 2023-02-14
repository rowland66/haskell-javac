{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}

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
, ValidTypeAbstraction(..)
, ValidTypeRefTypeDeclaration(..)
, ValidTypeValue(..)
, ValidTypeApplicationTarget(..)
, ValidTypeTerm(..)
, ValidTypeConstructorInvocation(..)
, ValidTypeSuperConstructorInvocation(..)
, ValidTypeAssignment(..)
, ValidTypeMethodImplementation(..)
, ValidTypeField(..)
, ValidTypeMethod(..)
, ValidTypeParameter(..)
, ValidTypeClazz(..)
, ValidTypeClassData
, transformToValidTypes
, TypeInfoData(..)
, getClassTypeInfoData
) where

import Control.Monad.Trans.State.Strict (StateT,get,put,evalStateT,runStateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad ( join, foldM )
import Text.Parsec.Pos (SourcePos)
import qualified Data.Validation as Val
import Data.Int (Int32)
import qualified Data.Map.Strict as Map
import qualified Data.Vector as Vector
import TextShow (showb,toText)
import qualified Data.Vector as V
import qualified Data.List as L
import Debug.Trace

import TypeCheckerTypes
import ClassPath ( ClassPath
                 , ClassDescriptor(..)
                 , ClassPathReferenceType(..)
                 , getClassPathValidType
                 , hasClass
                 , createValidTypeClassTypeObject
                 , getClassPathClassType
                 , ClassPathReferenceType
                 , eraseParameterizedType
                 )
import Parser2
import qualified Control.Applicative

type ClassData = (ClassPath,LocalClasses)

data TypeInfoData = LocalTypeInfoData ValidTypeClazz | ClassPathTypeInfoData ClassDescriptor

typeValidatorValidTypeName :: QualifiedName -> TypeCheckerValidTypeQualifiedNameWrapper
typeValidatorValidTypeName qn = TypeCheckerValidTypeQualifiedNameWrapper { getValidTypeQName = qn
                                                                         , isValidTypeQNameInClasspath = False
                                                                         }

data ValidTypeAbstraction = ValidTypeFieldAccess SourcePos SimpleName
                          | ValidTypeMethodInvocation SourcePos SimpleName [ValidTypeTerm]
                          | ValidTypeSuperMethodInvocation SourcePos SimpleName [ValidTypeTerm]
                          deriving Show

data ValidTypeValue = ValidTypeVariable SourcePos SimpleName
                    | ValidTypeIntegerLit SourcePos Int32
                    | ValidTypeStringLit SourcePos String
                    | ValidTypeBooleanLit SourcePos Bool
                    | ValidTypeObjectCreation SourcePos TypeCheckerClassReferenceTypeWrapper [ValidTypeTerm]
                    deriving Show

data ValidTypeApplicationTarget = ValidTypeApplicationTargetTerm ValidTypeTerm
                                | ValidTypeApplicationTargetTypeName ValidTypeRefTypeDeclaration
                                deriving Show

data ValidTypeTerm = ValidTypeValue ValidTypeValue
                   | ValidTypeApplication ValidTypeApplicationTarget ValidTypeAbstraction
                   | ValidTypeConditional ValidTypeTerm ValidTypeTerm ValidTypeTerm
                   | ValidTypeCast ValidTypeRefTypeDeclaration ValidTypeTerm
                   deriving Show


data ValidTypeParameter = ValidTypeParameter { vpName :: (SimpleName, SourcePos)
                                             , vpType :: TypeCheckerClassReferenceTypeWrapper
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

vectorToString :: Show a => Vector.Vector a -> String
vectorToString = Vector.foldr join ""
               where
                   join e s = show e ++
                                if null s
                                    then ""
                                    else "," ++ s


data ValidTypeRefTypeDeclaration = ValidTypeRefTypeDeclaration !SourcePos !TypeCheckerClassReferenceTypeWrapper deriving Show

data LocalReferenceType = LocalClassTypeReferenceType TypeCheckerClassReferenceTypeWrapper deriving (Show,Eq)

instance TypeCheckerReferenceType LocalReferenceType where
  getTypeCheckerReferenceTypeClass (LocalClassTypeReferenceType crtw) = 
    Just crtw
  getTypeCheckerReferenceTypeTypeVariable _ = Nothing
  getTypeCheckerReferenceTypeArray _ = Nothing
{--
data ValidTypeClassType = LocalCT LocalClassReferenceType | ClassPathCT ClassPathClassReferenceType deriving (Show)

instance Eq ValidTypeClassType where
  (==) (LocalCT (LocalClassReferenceType sn1 _)) (LocalCT (LocalClassReferenceType sn2 _)) = sn1 == sn2
  (==) (LocalCT (LocalClassReferenceType sn1 _)) (ClassPathCT cpcrt) =
    let (CPClassReferenceType sn2 _ ) = eraseParameterizedType cpcrt
      in getValidTypeQName sn1 == getValidTypeQName sn2
  (==) cpct@(ClassPathCT _) lct@(LocalCT _) = lct == cpct
  (==) (ClassPathCT cpcrt1) (ClassPathCT cpcrt2) = cpcrt1 == cpcrt2

instance TypeCheckerValidTypeQualifiedName ValidTypeClassType where
  getValidTypeQName (LocalCT (LocalClassReferenceType sn _)) = getValidTypeQName sn
  getValidTypeQName (ClassPathCT (CPClassReferenceType sn _)) = getValidTypeQName sn
  isValidTypeQNameInClasspath _ = False

instance TypeCheckerClassReferenceType ValidTypeClassType where
  getValidTypeRefTypeTypeName (LocalCT (LocalClassReferenceType vtn _)) = TypeCheckerValidTypeQualifiedNameWrapper vtn
  getValidTypeRefTypeTypeName (ClassPathCT cprt) = getValidTypeRefTypeTypeName cprt
  getValidTypeRefTypeTypeArguments (LocalCT _) = Nothing
  getValidTypeRefTypeTypeArguments (ClassPathCT cprt) = getValidTypeRefTypeTypeArguments cprt

-}

data ValidTypeField = ValidTypeField { vfName :: (SimpleName, SourcePos)
                                     , vfType :: TypeCheckerClassReferenceTypeWrapper
                                     } deriving Show

data ValidTypeMethod = ValidTypeMethod { vmName :: (SimpleName, SourcePos)
                                       , vmAccessFlags :: [MethodAccessFlag]
                                       , vmType :: TypeCheckerClassReferenceTypeWrapper
                                       , vmParams :: V.Vector ValidTypeParameter
                                       , vmMaybeImpl :: Maybe ValidTypeMethodImplementation
                                       } deriving Show

data ValidTypeClazz = ValidTypeClazz { vcAccessFlags :: [ClassAccessFlag]
                                     , vcName :: TypeCheckerValidTypeQualifiedNameWrapper
                                     , vcSourcePos :: SourcePos
                                     , vcParent :: (TypeCheckerClassReferenceTypeWrapper, SourcePos)
                                     , vcFields :: [ValidTypeField]
                                     , vcMethods :: [ValidTypeMethod]
                                     } deriving Show


type ValidTypeClassData = (ClassPath,Map.Map TypeCheckerValidTypeQualifiedNameWrapper ValidTypeClazz)

{--
data ResolvedTypeArgument = ResolvedClassTypeArgument (Maybe ValidTypeWildcardIndicator) ResolvedClassType
                          | ResolvedAnyTypeArgument
                          deriving (Show,Eq)

data ResolvedClassType = ResolvedClassType ValidTypeName (Vector.Vector ResolvedTypeArgument) deriving (Show,Eq)

adaptValidTypeReferenceType :: ValidTypeClassType -> ValidTypeReferenceType
adaptValidTypeReferenceType (LocalCT lct) = LocalRT (LocalClassTypeReferenceType lct)
adaptValidTypeReferenceType (ClassPathCT (CPClassReferenceType vtn maybeTypeArgs)) = ClassPathRT (CPClassReferenceType vtn maybeTypeArgs)

getValidTypeReferenceTypeClassPath :: ClassPathReferenceType -> ValidTypeReferenceType
getValidTypeReferenceTypeClassPath (CPClassRefType vtn maybeTypeArgs)= ClassPathRT (CPClassReferenceType vtn maybeTypeArgs)
getValidTypeReferenceTypeClassPath _ = undefined


getValidTypeClassTypeClassPath :: ClassPathClassReferenceType -> ValidTypeClassType
getValidTypeClassTypeClassPath = ClassPathCT
-}

transformToValidTypes :: StateT ClassData IO (Either [TypeError] [ValidTypeClazz])
transformToValidTypes = do
  (_,classMap) <- get
  Val.toEither <$> foldM (\validate clazz -> do
    validTypeClassV <- getValidTypeClass clazz
    return $ (:) <$> validTypeClassV <*> validate) (Val.Success []) (Map.elems classMap)

getValidTypeClass :: Clazz2 -> StateT ClassData IO (Val.Validation [TypeError] ValidTypeClazz)
getValidTypeClass cls@(NewClazz2 pos _ vcAccessFlags nm _ _ _) = do
  let vcName = nm
  validTypeParentV <- Val.fromEither <$> getClassParentValidType cls
  validTypeFieldsV <- getValidTypeFields cls
  validTypeMethodsV <- Val.fromEither <$> getValidTypeMethods cls
  return $ ValidTypeClazz vcAccessFlags (typeValidatorValidTypeName nm) pos <$> validTypeParentV <*> validTypeFieldsV <*> validTypeMethodsV

getClassParentValidType :: Clazz2 -> StateT ClassData IO (Either [TypeError] (TypeCheckerClassReferenceTypeWrapper, SourcePos))
getClassParentValidType (NewClazz2 pos _ _ _ ExtendsObject _ _) =
  return $
    Right (createValidTypeClassTypeObject, pos)
getClassParentValidType (NewClazz2 _ _ _ _ (NewExtends pos parent) _ _) = do
  cond <- getValidTypeQualifiedName parent
  case cond of
    Just vtn -> return $ Right (TypeCheckerClassReferenceTypeWrapper vtn Nothing, pos)
    Nothing -> return $ Left [TypeError ("Undefined type: "++show parent) pos]

getValidTypeFields :: Clazz2 -> StateT ClassData IO (Val.Validation [TypeError] [ValidTypeField])
getValidTypeFields (NewClazz2 _ _ _ _ _ fields _) = do
  foldM
    (\fieldList field@(NewField (ClassType pos tp tpargs) npos nm) ->
      do
        cond <- getValidTypeQualifiedName tp
        mappedTypeArgsE <- mapValidTypeTypeArguments tpargs
        let validTypeFieldV =
              case cond of
                Just vtn -> case mappedTypeArgsE of
                  Right mappedTypeArgs -> 
                    Val.Success (ValidTypeField{vfName=(nm,npos), vfType=crtw})
                    where
                      crtw = 
                        TypeCheckerClassReferenceTypeWrapper 
                          vtn (Just (V.fromList mappedTypeArgs))
                  Left errors -> Val.Failure errors
                Nothing -> Val.Failure [TypeError ("Invalid type name: "++show tp) pos]
        return $ (:) <$> validTypeFieldV <*> fieldList)
    (Val.Success [])
    fields

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
  returnValidTypeV <- Val.fromEither <$> getMethodReturnValidType method
  validTypeParamsV <- Val.fromEither <$> getValidTypeParams params
  validTypeExpressionV <- Val.fromEither <$> getMethodValidTypeExpression method
  return $ Val.toEither (ValidTypeMethod (nm,pos) vmAccessFlags <$> returnValidTypeV <*> fmap V.fromList validTypeParamsV <*> validTypeExpressionV)

getMethodReturnValidType :: Method -> StateT ClassData IO (Either [TypeError] TypeCheckerClassReferenceTypeWrapper)
getMethodReturnValidType (NewMethod pos _ _ _ tp _ _) = do
  maybeValidTypeName <- getValidTypeQualifiedName tp
  return $ case maybeValidTypeName of
    Just vtqnw -> Right (TypeCheckerClassReferenceTypeWrapper vtqnw Nothing)
    Nothing -> Left [TypeError ("Undefined type: "++show tp) pos]


getValidTypeParams :: [Parameter] -> StateT ClassData IO (Either [TypeError] [ValidTypeParameter])
getValidTypeParams = fmap (fmap reverse) <$> foldM (\either (NewParameter pos tp nmpos nm) ->
    do
      cond <- getValidTypeQualifiedName tp
      case either of
        Left typeErrors -> return $ Left (case cond of Nothing -> TypeError ("Undefined type: "++show tp) pos:typeErrors; Just _ -> typeErrors)
        Right typeList -> case cond of
          Just vtqnw -> return $ Right 
            (ValidTypeParameter 
              (nm,nmpos) 
              (TypeCheckerClassReferenceTypeWrapper vtqnw Nothing):typeList)
          Nothing -> return $ Left [TypeError ("Undefined type: "++show tp) pos]) (Right [])

{-- Get a list of terms from the arguments to a constructor or methdod -}
getTermValidTypeArguments :: [Term] -> StateT ClassData IO (Either [TypeError] [ValidTypeTerm])
getTermValidTypeArguments = fmap (fmap reverse) <$> foldM (\either t ->
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
  validTypeArgsE <- getTermValidTypeArguments args
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
  validTypeArgsE <- getTermValidTypeArguments args
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
getValidTypeTerm (Value (ObjectCreation pos (ClassType tppos tp _) args)) = do
  maybeValidTypeName <- getValidTypeQualifiedName tp
  validTypeArgumentsE <- getTermValidTypeArguments args
  rtrn <- case maybeValidTypeName of
    Nothing -> case validTypeArgumentsE of
      Left errors -> return $ Left $ errors++[TypeError ("Undefined type: "++show tp) pos]
      Right _ -> return $ Left [TypeError ("Undefined type: "++show tp) pos]
    Just vtqnw -> case validTypeArgumentsE of
      Left errors -> return $ Left errors
      Right validTypeArguments -> return $ Right 
        (ValidTypeValue 
          (ValidTypeObjectCreation pos 
            (TypeCheckerClassReferenceTypeWrapper 
              vtqnw Nothing) 
              validTypeArguments))
  return $ trace ("getValidTypeTerm@@ "++show args) rtrn
getValidTypeTerm (Value (ObjectCreation pos (TypeVariable tppos tpvar) args)) = undefined
getValidTypeTerm (Cast (ClassType pos tp _) term) = do
  maybeValidTypeName <- getValidTypeQualifiedName tp
  validTypeTermE <- getValidTypeTerm term
  return $ case maybeValidTypeName of
    Nothing -> case validTypeTermE of
      Left termTypeErrors -> Left $ termTypeErrors++[TypeError ("Undefined type: "++show tp) pos]
      Right _ -> Left [TypeError ("Undefined type: "++show tp) pos]
    Just vtqnw -> case validTypeTermE of
      Left termTypeErrors -> Left termTypeErrors
      Right validTypeTerm -> Right 
        (ValidTypeCast 
          (ValidTypeRefTypeDeclaration 
            pos 
            (TypeCheckerClassReferenceTypeWrapper 
              vtqnw Nothing))
          validTypeTerm)
getValidTypeTerm (Cast (TypeVariable pos tpvar) term) = undefined
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
getValidTypeTerm (Application (ApplicationTargetTypeName (ClassType tppos tp _)) (FieldAccess pos nm)) = do
  maybeValidTypeName <- getValidTypeQualifiedName tp
  return $ case maybeValidTypeName of
    Nothing -> Left [TypeError "Type not valid in this context" tppos]
    Just vtqnw -> getValidTypeApplication 
      tppos 
      (TypeCheckerClassReferenceTypeWrapper vtqnw Nothing)
      (ValidTypeFieldAccess pos nm)
getValidTypeTerm (Application (ApplicationTargetTypeName (TypeVariable tppos tpvar)) (FieldAccess pos nm)) = undefined
getValidTypeTerm (Application (ApplicationTargetTypeName (ClassType tppos tp _)) (MethodInvocation pos nm params)) = do
  maybeValidTypeName <- getValidTypeQualifiedName tp
  validTypeParamsE <- fmap reverse <$> foldM (\either t'' -> do
      vtp <- getValidTypeTerm t''
      return $ consEither vtp either) (Right []) params
  return $ case validTypeParamsE of
    Left typeErrors -> case maybeValidTypeName of
      Nothing -> Left $ TypeError "Type not valid in this context" tppos : typeErrors
      Just _ -> Left typeErrors
    Right validTypeParams -> case maybeValidTypeName of
      Nothing -> Left [TypeError "Type not valid in this context" tppos]
      Just vtqnw -> getValidTypeApplication 
        tppos 
        (TypeCheckerClassReferenceTypeWrapper vtqnw Nothing)
        (ValidTypeMethodInvocation pos nm validTypeParams)
getValidTypeTerm (Application (ApplicationTargetTypeName (TypeVariable tppos tpvar)) (MethodInvocation pos nm params)) = undefined
getValidTypeTerm (Application (ApplicationTargetTypeName (ClassType tppos tp _)) (SuperMethodInvocation pos nm params)) = undefined
getValidTypeTerm (Application (ApplicationTargetTypeName (TypeVariable tppos tpvar)) (SuperMethodInvocation pos nm params)) = undefined
getValidTypeTerm (Value (Variable pos sn)) = return $ Right (ValidTypeValue (ValidTypeVariable pos sn))
getValidTypeTerm (Value (IntegerLit pos i)) = return $ Right (ValidTypeValue (ValidTypeIntegerLit pos i))
getValidTypeTerm (Value (StringLit pos s)) = return $ Right (ValidTypeValue (ValidTypeStringLit pos s))
getValidTypeTerm (Value (BooleanLit pos b)) = return $ Right (ValidTypeValue (ValidTypeBooleanLit pos b))
getValidTypeTerm (Conditional cond ifTerm elseTerm) = do
  Val.toEither <$> getValidTypeConditional cond ifTerm elseTerm

getValidTypeApplication :: SourcePos -> TypeCheckerClassReferenceTypeWrapper -> ValidTypeAbstraction -> Either [TypeError] ValidTypeTerm
getValidTypeApplication tppos crtw@(TypeCheckerClassReferenceTypeWrapper _ typeArgs) abstraction =
  case typeArgs of
    Nothing ->
      Right (ValidTypeApplication
        (ValidTypeApplicationTargetTypeName (ValidTypeRefTypeDeclaration tppos crtw))
        abstraction)
    _ -> Left [TypeError "Type arguments not valid in this context" tppos]

getValidTypeConditional :: Term -> Term -> Term -> StateT ClassData IO (Val.Validation [TypeError] ValidTypeTerm)
getValidTypeConditional cond ifTerm elseTerm = do
  condV <- Val.fromEither <$> getValidTypeTerm cond
  ifTermV <- Val.fromEither <$> getValidTypeTerm ifTerm
  elseTermV <- Val.fromEither <$> getValidTypeTerm elseTerm
  return $ ValidTypeConditional <$> condV <*> ifTermV <*> elseTermV

getValidTypeQualifiedName :: QualifiedName -> StateT ClassData IO (Maybe TypeCheckerValidTypeQualifiedNameWrapper)
getValidTypeQualifiedName tp = do
  (classPath,classMap) <- get
  return $ if Map.member tp classMap
    then Just (typeValidatorValidTypeName tp)
    else
      getClassPathClassType classPath tp

{--
getValidReferenceType :: ReferenceType -> StateT ClassData IO (Val.Validation [TypeError] ValidTypeReferenceType)
getValidReferenceType (ClassType pos qn typeArgs) = do
  maybeValidTypeName <- getValidTypeClassType qn
  case maybeValidTypeName of
    Nothing -> return $ Val.Failure [TypeError ("Invalid type name: "++show qn) pos]
    Just vtn -> do
      validRefTypesV <- foldM (\validate typeArg -> do
        vrt <- case typeArg of
          (ReferenceTypeArgument typeArgRefType) -> getValidReferenceType typeArgRefType
          (WildcardArgument _) -> undefined
        return $ (:) <$>  vrt <*> validate)
        (Val.Success [])
        typeArgs
      return $ case Val.toEither validRefTypesV of
        Right validRefTypes -> case vtn of
          LocalCT lct -> Val.Success (LocalRT (LocalClassTypeReferenceType lct))
          ClassPathCT cpcrt -> Val.Success (ClassPathRT cpcrt)
        Left err -> Val.Failure err
getValidReferenceType (TypeVariable pos sn) = undefined
-}

getClassTypeInfoData :: TypeCheckerValidTypeQualifiedNameWrapper -> StateT ValidTypeClassData IO TypeInfoData
getClassTypeInfoData vtqnw = do
  (classPath, classMap) <- get
  if isValidTypeQNameInClasspath vtqnw
    then lift $ ClassPathTypeInfoData <$> evalStateT (getClassPathValidType vtqnw) classPath
    else return $ LocalTypeInfoData $ classMap Map.! vtqnw

mapValidTypeTypeArgument :: TypeArgument -> StateT ClassData IO (Either [TypeError] TypeCheckerTypeArgument)
mapValidTypeTypeArgument (ReferenceTypeArgument (ClassType tppos qn typeArgs)) = do
  maybeVtqnw <- getValidTypeQualifiedName qn
  case maybeVtqnw of
    Nothing -> return $ Left $ [TypeError ("Type argument is not a valid type: "++show qn) tppos]
    Just vtqnw -> case typeArgs of
      [] -> return $ Right $ 
        TypeCheckerTypeArgument 
          Nothing 
          (TypeCheckerReferenceTypeWrapper (LocalClassTypeReferenceType (TypeCheckerClassReferenceTypeWrapper vtqnw Nothing)))
      ta : tas -> do
        eitherValidTypeArgsOrError <- mapValidTypeTypeArguments tas
        return $ case eitherValidTypeArgsOrError of
          Left tes -> Left tes
          Right tas' -> Right $ 
            TypeCheckerTypeArgument 
              Nothing 
              (TypeCheckerReferenceTypeWrapper 
                (LocalClassTypeReferenceType
                  (TypeCheckerClassReferenceTypeWrapper 
                    vtqnw 
                    (Just (V.fromList tas')))))
mapValidTypeTypeArgument (ReferenceTypeArgument (TypeVariable pos sn)) = undefined
mapValidTypeTypeArgument (WildcardArgument wildcardBounds) = undefined

mapValidTypeTypeArguments :: [TypeArgument] -> StateT ClassData IO (Either [TypeError] [TypeCheckerTypeArgument])
mapValidTypeTypeArguments typeArgs = do
  a <- mapM (\ta -> mapValidTypeTypeArgument ta) typeArgs
  return $ foldr
            (\eitherTypeArgOrError result -> case eitherTypeArgOrError of
                Left newErrors -> case result of
                  Left existingErrors -> Left (newErrors ++ existingErrors)
                  Right _ -> Left newErrors
                Right newTa -> case result of
                  existingEither@(Left _) -> existingEither
                  Right existingTa -> Right (newTa:existingTa))
            (Right [])
            a
