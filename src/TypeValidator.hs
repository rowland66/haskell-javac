{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StrictData #-}

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
, ValidTypeTypeName(..)
, transformToValidTypes
, TypeInfoData(..)
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
import Control.Conditional (if')
import Debug.Trace

import TypeCheckerTypes
import ClassPath ( ClassPath
                 , ClassDescriptor(..)
                 , getClassPathValidType
                 , hasClass
                 , createValidTypeClassTypeObject
                 , getClassPathClassType
                 )
import Parser2
import qualified Control.Applicative
import Data.Foldable (foldrM)

type ClassData = (ClassPath,LocalClasses)

data TypeInfoData = LocalTypeInfoData ValidTypeClazz | ClassPathTypeInfoData ClassDescriptor

typeValidatorValidTypeName :: QualifiedName -> TypeCheckerValidTypeQualifiedNameWrapper
typeValidatorValidTypeName qn = TypeCheckerValidTypeQualifiedNameWrapper { getValidTypeQName = qn
                                                                         }

data ValidTypeAbstraction = ValidTypeFieldAccess SourcePos SimpleName
                          | ValidTypeMethodInvocation SourcePos SimpleName [ValidTypeTerm] [TypeCheckerTypeArgument]
                          | ValidTypeSuperMethodInvocation SourcePos SimpleName [ValidTypeTerm]
                          deriving Show

data ValidTypeValue = ValidTypeVariable SourcePos SimpleName
                    | ValidTypeIntegerLit SourcePos Int32
                    | ValidTypeStringLit SourcePos String
                    | ValidTypeBooleanLit SourcePos Bool
                    | ValidTypeObjectCreation SourcePos TypeCheckerClassReferenceTypeWrapper [ValidTypeTerm] [TypeCheckerTypeArgument]
                    deriving Show

data ValidTypeApplicationTarget = ValidTypeApplicationTargetTerm ValidTypeTerm
                                | ValidTypeApplicationTargetTypeName ValidTypeTypeName
                                deriving Show

data ValidTypeTerm = ValidTypeValue ValidTypeValue
                   | ValidTypeApplication ValidTypeApplicationTarget ValidTypeAbstraction
                   | ValidTypeConditional ValidTypeTerm ValidTypeTerm ValidTypeTerm
                   | ValidTypeCast ValidTypeRefTypeDeclaration ValidTypeTerm
                   deriving Show


data ValidTypeParameter = ValidTypeParameter { vpName :: (SimpleName, SourcePos)
                                             , vpType :: TypeCheckerJavaType
                                             } deriving (Show,Eq)

data ValidTypeConstructorInvocation = ValidTypeConstructorInvocation SourcePos [ValidTypeTerm] deriving Show

data ValidTypeSuperConstructorInvocation = ValidTypeSuperConstructorInvocation SourcePos [ValidTypeTerm] deriving Show

data ValidTypeAssignment = ValidTypeAssignment { vaLeftHandTerm :: ValidTypeTerm
                                               , vaRightHandTerm :: ValidTypeTerm
                                               } deriving Show

data ValidTypeMethodImplementation = ValidTypeMethodImplementation { vmiTerm :: ValidTypeTerm}
                                   | ValidTypeConstructorImplementation { vmiConstructorInvocation :: Either ValidTypeConstructorInvocation ValidTypeSuperConstructorInvocation
                                                                        , vmiAssignments :: [ValidTypeAssignment]
                                                                        } deriving Show

mkValidTypeConstructorImplementation :: ValidTypeConstructorInvocation -> [ValidTypeAssignment] -> ValidTypeMethodImplementation
mkValidTypeConstructorImplementation constructorInvocation vmiAssignments =
  let vmiConstructorInvocation = Left constructorInvocation
  in
    ValidTypeConstructorImplementation{..}

mkValidTypeSuperConstructorImplementation :: ValidTypeSuperConstructorInvocation -> [ValidTypeAssignment] -> ValidTypeMethodImplementation
mkValidTypeSuperConstructorImplementation constructorInvocation vmiAssignments =
  let vmiConstructorInvocation = Right constructorInvocation
  in
    ValidTypeConstructorImplementation{..}

vectorToString :: Show a => Vector.Vector a -> String
vectorToString = Vector.foldr join ""
               where
                   join e s = show e ++
                                if null s
                                    then ""
                                    else "," ++ s


data ValidTypeRefTypeDeclaration = ValidTypeRefTypeDeclaration SourcePos TypeCheckerReferenceTypeWrapper deriving Show

data ValidTypeTypeName = ValidTypeTypeName SourcePos TypeCheckerValidTypeQualifiedNameWrapper deriving Show

data ValidTypeField = ValidTypeField { vfName :: (SimpleName, SourcePos)
                                     , vfType :: TypeCheckerJavaType
                                     , vfClassName :: TypeCheckerValidTypeQualifiedNameWrapper
                                     } deriving Show

data ValidTypeMethod = ValidTypeMethod { vmName :: (SimpleName, SourcePos)
                                       , vmAccessFlags :: [MethodAccessFlag]
                                       , vmType :: TypeCheckerJavaType
                                       , vmParams :: V.Vector ValidTypeParameter
                                       , vmMaybeImpl :: Maybe ValidTypeMethodImplementation
                                       , vmClassName :: TypeCheckerValidTypeQualifiedNameWrapper
                                       } deriving Show

data ValidTypeClazz = ValidTypeClazz { vcAccessFlags :: [ClassAccessFlag]
                                     , vcName :: TypeCheckerValidTypeQualifiedNameWrapper
                                     , vcSourcePos :: SourcePos
                                     , vcParent :: (TypeCheckerClassReferenceTypeWrapper, SourcePos)
                                     , vcFields :: [ValidTypeField]
                                     , vcMethods :: [ValidTypeMethod]
                                     } deriving Show


type ValidTypeClassData = (ClassPath,Map.Map TypeCheckerValidTypeQualifiedNameWrapper ValidTypeClazz)

transformToValidTypes :: StateT ClassData IO (Val.Validation [TypeError] [ValidTypeClazz])
transformToValidTypes = do
  (_,classMap) <- get
  foldrM (\clazz accum -> do
      validTypeClassV <- getValidTypeClass clazz
      return $ (:) <$> validTypeClassV <*> accum)
    (Val.Success [])
    (Map.elems classMap)

getValidTypeClass :: Clazz2 -> StateT ClassData IO (Val.Validation [TypeError] ValidTypeClazz)
getValidTypeClass cls@(NewClazz2 pos _ vcAccessFlags nm _ _ _) = do
  let validTypeQualifiedName = typeValidatorValidTypeName nm
  validTypeParentV <- getClassParentValidType cls
  validTypeFieldsV <- getValidTypeFields cls validTypeQualifiedName
  validTypeMethodsV <- getValidTypeMethods cls validTypeQualifiedName
  return $ ValidTypeClazz vcAccessFlags validTypeQualifiedName pos <$> validTypeParentV <*> validTypeFieldsV <*> validTypeMethodsV

getClassParentValidType :: Clazz2 -> StateT ClassData IO (Val.Validation [TypeError] (TypeCheckerClassReferenceTypeWrapper, SourcePos))
getClassParentValidType (NewClazz2 pos _ _ _ ExtendsObject _ _) =
  return $
    Val.Success (createValidTypeClassTypeObject, pos)
getClassParentValidType (NewClazz2 _ _ _ _ (NewExtends pos parent typeArgs) _ _) = do
  vtqnE <- validateM [TypeError ("Undefined type: "++show parent) pos] getValidTypeQualifiedName parent
  typeArgsE <- 
    (\(Val.Success tas) -> 
      case tas of 
        [] -> Val.Success Nothing; 
        xs -> Val.Success (Just (V.fromList xs))) 
    <$> getValidTypeTypeArguments typeArgs
  return $ (,) <$> (TypeCheckerClassReferenceTypeWrapper <$> vtqnE <*> typeArgsE) <*> pure pos

getValidTypeFields :: Clazz2 -> TypeCheckerValidTypeQualifiedNameWrapper -> StateT ClassData IO (Val.Validation [TypeError] [ValidTypeField])
getValidTypeFields (NewClazz2 _ _ _ _ _ fields _) vtqn =
  foldrM
    (\field fieldList -> do
      validTypeFieldE <- getValidTypeField vtqn field
      return $ (:) <$> validTypeFieldE <*> fieldList)
    (Val.Success [])
    fields

getValidTypeField :: TypeCheckerValidTypeQualifiedNameWrapper -> Field -> StateT ClassData IO (Val.Validation [TypeError] ValidTypeField)
getValidTypeField vtqn field@(NewField (JavaReferenceType (ClassType pos tp tpargs)) npos nm) = do
  vtqnE <- validateM [TypeError ("Invalid type name: "++show tp) pos] getValidTypeQualifiedName tp
  validTypeTypeArgumentsE <- mapValidTypeTypeArguments tpargs
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
        vtqnE <*>
        fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeTypeArgumentsE
  let jtE = TypeCheckerJavaReferenceType <$> (TypeCheckerClassRefType <$> crtwE)
  let validTypeFieldV = ValidTypeField (nm,npos) <$> jtE <*> pure vtqn
  return validTypeFieldV
getValidTypeField vtqn field@(NewField (JavaReferenceType _) npos nm) = undefined
getValidTypeField vtqn field@(NewField (JavaPrimitiveType (PrimitiveIntegralType pos)) npos nm) = 
  return $ Val.Success $
    ValidTypeField (nm,npos) (TypeCheckerJavaPrimitiveType TypeCheckerIntegerPrimitiveType) vtqn
getValidTypeField vtqn field@(NewField (JavaPrimitiveType (PrimitiveBooleanType pos)) npos nm) = 
  return $ Val.Success $ 
    ValidTypeField (nm,npos) (TypeCheckerJavaPrimitiveType TypeCheckerBooleanPrimitiveType) vtqn

consEither :: Either [a] b -> Either [a] [b] -> Either [a] [b]
consEither head list =
  case list of
    Left xs -> case head of
      Left x -> Left (x++xs)
      Right _ -> Left xs
    Right xs -> case head of
      Right x -> Right (x:xs)
      Left x -> Left x

getValidTypeMethods :: Clazz2 -> TypeCheckerValidTypeQualifiedNameWrapper -> StateT ClassData IO (Val.Validation [TypeError] [ValidTypeMethod])
getValidTypeMethods (NewClazz2 _ _ _ _ _ _ methods) vtqnw =
  foldrM (\method either -> do
    validTypeMethodE <- getValidTypeMethod method vtqnw
    return $ (:) <$> validTypeMethodE <*> either)
  (Val.Success [])
  methods

getValidTypeMethod :: Method -> TypeCheckerValidTypeQualifiedNameWrapper -> StateT ClassData IO (Val.Validation [TypeError] ValidTypeMethod)
getValidTypeMethod method@(NewMethod pos vmAccessFlags nm params _ _ _) vtqnw = do
  returnValidTypeV <- getMethodReturnValidType method
  validTypeParamsV <- getValidTypeParams params
  validTypeExpressionV <- getMethodValidTypeExpression method
  return $ ValidTypeMethod (nm,pos) vmAccessFlags <$>
    returnValidTypeV <*>
    fmap V.fromList validTypeParamsV <*>
    validTypeExpressionV <*>
    pure vtqnw

getMethodReturnValidType :: Method -> StateT ClassData IO (Val.Validation [TypeError] TypeCheckerJavaType)
getMethodReturnValidType (NewMethod _ _ _ _ (JavaReferenceType tp@(ClassType pos qn typeArgs)) _ _) = do
  validTypeNameE <- validateM [TypeError ("Undefined type: "++show tp) pos] getValidTypeQualifiedName qn
  validTypeTypeArgumentsE <- mapValidTypeTypeArguments typeArgs
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
        validTypeNameE <*>
        fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeTypeArgumentsE
  let jtE = TypeCheckerJavaReferenceType <$> (TypeCheckerClassRefType <$> crtwE)
  return jtE
getMethodReturnValidType (NewMethod _ _ _ _ (JavaReferenceType _) _ _) = undefined
getMethodReturnValidType (NewMethod _ _ _ _ (JavaPrimitiveType (PrimitiveIntegralType pos)) _ _) = 
  return $ Val.Success $
    TypeCheckerJavaPrimitiveType TypeCheckerIntegerPrimitiveType
getMethodReturnValidType (NewMethod _ _ _ _ (JavaPrimitiveType (PrimitiveBooleanType pos)) _ _) = 
  return $ Val.Success $
    TypeCheckerJavaPrimitiveType TypeCheckerIntegerPrimitiveType

getValidTypeParams :: [Parameter] -> StateT ClassData IO (Val.Validation [TypeError] [ValidTypeParameter])
getValidTypeParams =
  foldrM (\param accum -> do
    vtpE <- getValidTypeParam param
    return $ (:) <$> vtpE <*> accum)
  (Val.Success [])

getValidTypeParam :: Parameter -> StateT ClassData IO (Val.Validation [TypeError] ValidTypeParameter)
getValidTypeParam (NewParameter (JavaReferenceType tp@(ClassType pos qn typeArgs)) nmpos nm) = do
  vtqnE <- validateM [TypeError ("Undefined type: "++show tp) pos] getValidTypeQualifiedName qn
  validTypeTypeArgumentsE <- mapValidTypeTypeArguments typeArgs
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
        vtqnE <*>
        fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeTypeArgumentsE
  let jtE = TypeCheckerJavaReferenceType <$> (TypeCheckerClassRefType <$> crtwE)
  return $ ValidTypeParameter (nm,nmpos) <$> jtE
getValidTypeParam (NewParameter (JavaReferenceType _) nmpos nm) = undefined
getValidTypeParam (NewParameter (JavaPrimitiveType (PrimitiveIntegralType pos)) nmpos nm) = 
  return $ Val.Success $ ValidTypeParameter (nm,nmpos) (TypeCheckerJavaPrimitiveType TypeCheckerIntegerPrimitiveType)
getValidTypeParam (NewParameter (JavaPrimitiveType (PrimitiveBooleanType pos)) nmpos nm) = 
  return $ Val.Success $ ValidTypeParameter (nm,nmpos) (TypeCheckerJavaPrimitiveType TypeCheckerBooleanPrimitiveType)

getValidTypeTypeArguments :: [TypeArgument] -> StateT ClassData IO (Val.Validation [TypeError] [TypeCheckerTypeArgument])
getValidTypeTypeArguments =
  foldrM (\typeArg accum -> do
    validTypeTypeArgE <- getValidTypeTypeArgument typeArg
    return $ (:) <$> validTypeTypeArgE <*> accum)
  (Val.Success [])

getValidTypeTypeArgument :: TypeArgument -> StateT ClassData IO (Val.Validation [TypeError] TypeCheckerTypeArgument)
getValidTypeTypeArgument (ReferenceTypeArgument tp@(ClassType pos qn typeArgs)) = do
  vtqnE <- validateM [TypeError ("Undefined type: "++show tp) pos] getValidTypeQualifiedName qn
  vtTypeArgsE <- getValidTypeTypeArguments typeArgs
  let maybeTypeArgsE = if' <$> (null <$> vtTypeArgsE) <*> pure Nothing <*> (Just <$> (Vector.fromList <$> vtTypeArgsE))
  let rtw = TypeCheckerClassRefType <$> (TypeCheckerClassReferenceTypeWrapper <$> vtqnE <*> maybeTypeArgsE)
  return $ TypeCheckerTypeArgument Nothing <$> rtw
getValidTypeTypeArgument (ReferenceTypeArgument tp@(TypeVariable pos sn)) = undefined
getValidTypeTypeArgument (WildcardArgument _ ) = undefined

{-- Get a list of terms from the arguments to a constructor or methdod -}
getTermValidTypeArguments :: [Term] -> StateT ClassData IO (Val.Validation [TypeError] [ValidTypeTerm])
getTermValidTypeArguments =
  foldrM (\term accum -> do
    validTypeTermE <- getValidTypeTerm term
    return $ (:) <$> validTypeTermE <*> accum)
  (Val.Success [])


getMethodValidTypeExpression :: Method -> StateT ClassData IO (Val.Validation [TypeError] (Maybe ValidTypeMethodImplementation))
getMethodValidTypeExpression (NewMethod _ _ _ _ _ _ (Just (MethodImpl term))) = do
  validTypeTermE <- getValidTypeTerm term
  return $ Just <$> (ValidTypeMethodImplementation <$> validTypeTermE)
getMethodValidTypeExpression (NewMethod _ _ _ _ _ _ (Just (ConstructorImpl (Left (NewConstructorInvocation pos args)) assignments))) = do
  validTypeAssignmentsE <- getValidTypeAssignments assignments
  validTypeArgsE <- getTermValidTypeArguments args
  let constructorInvocationE = ValidTypeConstructorInvocation pos <$> validTypeArgsE
  return $ Just <$> (mkValidTypeConstructorImplementation <$> constructorInvocationE <*> validTypeAssignmentsE)
getMethodValidTypeExpression (NewMethod _ _ _ _ _ _ (Just (ConstructorImpl (Right (NewSuperConstructorInvocation pos args)) assignments))) = do
  validTypeAssignmentsE <- getValidTypeAssignments assignments
  validTypeArgsE <- getTermValidTypeArguments args
  let constructorInvocationE = ValidTypeSuperConstructorInvocation pos <$> validTypeArgsE
  return $ Just <$> (mkValidTypeSuperConstructorImplementation <$> constructorInvocationE <*> validTypeAssignmentsE)
getMethodValidTypeExpression (NewMethod _ _ _ _ _ _ Nothing) =
  return $ Val.Success Nothing

getValidTypeAssignments :: [Assignment]-> StateT ClassData IO (Val.Validation [TypeError] [ValidTypeAssignment])
getValidTypeAssignments = foldrM (\assignment accum -> do
  validTypeAssignmentE <- getValidTypeAssignment assignment
  return $ (:) <$> validTypeAssignmentE <*> accum)
  (Val.Success [])

getValidTypeAssignment :: Assignment -> StateT ClassData IO (Val.Validation [TypeError] ValidTypeAssignment)
getValidTypeAssignment (NewAssignment lpos t1 rpos t2) = do
  lhTermE <- getValidTypeTerm t1
  rhTermE <- getValidTypeTerm t2
  return $ ValidTypeAssignment <$> lhTermE <*> rhTermE

{-- Convert a term to a valid term by confirming the validity of the term.
-}
getValidTypeTerm :: Term -> StateT ClassData IO (Val.Validation [TypeError] ValidTypeTerm)
getValidTypeTerm (Value (ObjectCreation pos (ClassType tppos tp typeArgs) args constructorTypeArgs)) = do
  validTypeNameE <- validateM [TypeError ("Undefined type: "++show tp) pos] getValidTypeQualifiedName tp
  validTypeArgumentsE <- getTermValidTypeArguments args
  validTypeTypeArgumentsE <- mapValidTypeTypeArguments typeArgs
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
        validTypeNameE <*>
        fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeTypeArgumentsE
  validTypeConstructorTypeArgsE <- getValidTypeTypeArguments typeArgs
  let vtocE = ValidTypeObjectCreation pos <$> crtwE <*> validTypeArgumentsE <*> validTypeConstructorTypeArgsE
  return $ ValidTypeValue <$> vtocE
getValidTypeTerm (Value (ObjectCreation pos (TypeVariable tppos tpvar) args constructorTypeArgs)) = undefined
getValidTypeTerm (Cast (ClassType pos tp typeArgs) term) = do
  validTypeNameE <- validateM [TypeError ("Undefined type: "++show tp) pos] getValidTypeQualifiedName tp
  validTypeTermE <- getValidTypeTerm term
  validTypeTypeArgumentsE <- mapValidTypeTypeArguments typeArgs
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
        validTypeNameE <*>
        fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeTypeArgumentsE
  let vtrtdE = ValidTypeRefTypeDeclaration pos <$> (TypeCheckerClassRefType <$> crtwE)
  return $ ValidTypeCast <$> vtrtdE <*> validTypeTermE
getValidTypeTerm (Cast (TypeVariable pos tpvar) term) = undefined
getValidTypeTerm (Application (ApplicationTargetTerm t) (FieldAccess pos nm)) = do
  validTypeTermE <- getValidTypeTerm t
  return $
    ValidTypeApplication <$>
      (ValidTypeApplicationTargetTerm <$> validTypeTermE) <*>
      pure (ValidTypeFieldAccess pos nm)
getValidTypeTerm (Application (ApplicationTargetTerm t) (MethodInvocation pos nm args typeArgs)) = do
  validTypeTermE <- getValidTypeTerm t
  validTypeArgsE <- getTermValidTypeArguments args
  validTypeTypeArgsE <- getValidTypeTypeArguments typeArgs
  let att = ValidTypeApplicationTargetTerm <$> validTypeTermE
  let mi = ValidTypeMethodInvocation pos nm <$> validTypeArgsE <*> validTypeTypeArgsE
  return $ ValidTypeApplication <$> att <*> mi
getValidTypeTerm (Application (ApplicationTargetTerm t) (SuperMethodInvocation pos nm args)) = do
  validTypeTermE <- getValidTypeTerm t
  validTypeArgsE <- getTermValidTypeArguments args
  return $
    ValidTypeApplication <$>
      (ValidTypeApplicationTargetTerm <$> validTypeTermE) <*>
      (ValidTypeSuperMethodInvocation pos nm <$> validTypeArgsE)
getValidTypeTerm (Application (ApplicationTargetTypeName (ClassType tppos tp _)) (FieldAccess pos nm)) = do
  validTypeNameE <- validateM [TypeError "Type not valid in this context" tppos] getValidTypeQualifiedName tp
  let attnE = ValidTypeApplicationTargetTypeName <$> (ValidTypeTypeName tppos <$> validTypeNameE)
  return $ ValidTypeApplication <$> attnE <*> pure (ValidTypeFieldAccess pos nm)
getValidTypeTerm (Application (ApplicationTargetTypeName (TypeVariable tppos tpvar)) (FieldAccess pos nm)) = undefined
getValidTypeTerm (Application (ApplicationTargetTypeName (ClassType tppos tp _)) (MethodInvocation pos nm args typeArgs)) = do
  vtqnE <- validateM [TypeError "Type not valid in this context" tppos] getValidTypeQualifiedName tp
  validTypeArgsE <- getTermValidTypeArguments args
  validTypeTypeArgsE <- getValidTypeTypeArguments typeArgs
  let vmiE = ValidTypeMethodInvocation pos nm <$> validTypeArgsE <*> validTypeTypeArgsE
  let attnE = ValidTypeApplicationTargetTypeName <$> (ValidTypeTypeName tppos <$> vtqnE)
  return $
    ValidTypeApplication <$> attnE <*> vmiE
getValidTypeTerm (Application (ApplicationTargetTypeName (ClassType tppos tp _)) (SuperMethodInvocation pos nm args)) = undefined

getValidTypeTerm (Application (ApplicationTargetTypeName (TypeVariable tppos tpvar)) (MethodInvocation pos nm params _)) = undefined
getValidTypeTerm (Application (ApplicationTargetTypeName (TypeVariable tppos tpvar)) (SuperMethodInvocation pos nm params)) = undefined
getValidTypeTerm (Value (Variable pos sn)) = return $ Val.Success (ValidTypeValue (ValidTypeVariable pos sn))
getValidTypeTerm (Value (IntegerLit pos i)) = return $ Val.Success (ValidTypeValue (ValidTypeIntegerLit pos i))
getValidTypeTerm (Value (StringLit pos s)) = return $ Val.Success (ValidTypeValue (ValidTypeStringLit pos s))
getValidTypeTerm (Value (BooleanLit pos b)) = return $ Val.Success (ValidTypeValue (ValidTypeBooleanLit pos b))
getValidTypeTerm (Conditional cond ifTerm elseTerm) = do
  getValidTypeConditional cond ifTerm elseTerm

getValidTypeConditional :: Term -> Term -> Term -> StateT ClassData IO (Val.Validation [TypeError] ValidTypeTerm)
getValidTypeConditional cond ifTerm elseTerm = do
  condV <- getValidTypeTerm cond
  ifTermV <- getValidTypeTerm ifTerm
  elseTermV <- getValidTypeTerm elseTerm
  return $ ValidTypeConditional <$> condV <*> ifTermV <*> elseTermV

getValidTypeQualifiedName :: QualifiedName -> StateT ClassData IO (Maybe TypeCheckerValidTypeQualifiedNameWrapper)
getValidTypeQualifiedName tp = do
  (classPath,classMap) <- get
  return $ if Map.member tp classMap
    then Just (typeValidatorValidTypeName tp)
    else getClassPathClassType classPath tp

validateM :: (Monad m) => e -> (a -> m(Maybe b)) -> a -> m(Val.Validation e b)
validateM e p a = do
  r <- p a
  case r of
    Nothing -> return $ Val.Failure e
    Just b -> return $ Val.Success b

mapValidTypeTypeArgument :: TypeArgument -> StateT ClassData IO (Val.Validation [TypeError] TypeCheckerTypeArgument)
mapValidTypeTypeArgument (ReferenceTypeArgument (ClassType tppos qn typeArgs)) = do
  vtqnwE <- validateM [TypeError ("Type argument is not a valid type: "++show qn) tppos] getValidTypeQualifiedName qn
  validTypeArgsE <- mapValidTypeTypeArguments typeArgs
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
        vtqnwE <*>
        fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeArgsE
      crtE = TypeCheckerClassRefType <$> crtwE
      in
        return $ TypeCheckerTypeArgument Nothing <$> crtE
mapValidTypeTypeArgument (ReferenceTypeArgument (TypeVariable pos sn)) = undefined
mapValidTypeTypeArgument (WildcardArgument wildcardBounds) = undefined

mapValidTypeTypeArguments :: [TypeArgument] -> StateT ClassData IO (Val.Validation [TypeError] [TypeCheckerTypeArgument])
mapValidTypeTypeArguments typeArgs = do
  validTypeArgsE <- mapM mapValidTypeTypeArgument typeArgs
  return $ foldr
    (\vtaE accum -> (:) <$> vtaE <*> accum)
    (Val.Success [])
    validTypeArgsE