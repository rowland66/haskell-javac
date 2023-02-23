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


data ValidTypeRefTypeDeclaration = ValidTypeRefTypeDeclaration SourcePos TypeCheckerClassReferenceTypeWrapper deriving Show

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
                                     , vfClassName :: TypeCheckerValidTypeQualifiedNameWrapper
                                     } deriving Show

data ValidTypeMethod = ValidTypeMethod { vmName :: (SimpleName, SourcePos)
                                       , vmAccessFlags :: [MethodAccessFlag]
                                       , vmType :: TypeCheckerClassReferenceTypeWrapper
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
getClassParentValidType (NewClazz2 _ _ _ _ (NewExtends pos parent) _ _) = do
  vtqnE <- validateM [TypeError ("Undefined type: "++show parent) pos] getValidTypeQualifiedName parent
  return $ (,) <$> (TypeCheckerClassReferenceTypeWrapper <$> vtqnE <*> pure Nothing) <*> pure pos

getValidTypeFields :: Clazz2 -> TypeCheckerValidTypeQualifiedNameWrapper -> StateT ClassData IO (Val.Validation [TypeError] [ValidTypeField])
getValidTypeFields (NewClazz2 _ _ _ _ _ fields _) vtqn = do
  foldrM
    (\field@(NewField (ClassType pos tp tpargs) npos nm) fieldList-> do
      vtqnE <- validateM [TypeError ("Invalid type name: "++show tp) pos] getValidTypeQualifiedName tp
      validTypeTypeArgumentsE <- mapValidTypeTypeArguments tpargs
      let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
            vtqnE <*>
            fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeTypeArgumentsE
      let validTypeFieldV = ValidTypeField (nm,npos) <$> crtwE <*> pure vtqn
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

getMethodReturnValidType :: Method -> StateT ClassData IO (Val.Validation [TypeError] TypeCheckerClassReferenceTypeWrapper)
getMethodReturnValidType (NewMethod _ _ _ _ tp@(ClassType pos qn typeArgs) _ _) = do
  validTypeNameE <- validateM [TypeError ("Undefined type: "++show tp) pos] getValidTypeQualifiedName qn
  validTypeTypeArgumentsE <- mapValidTypeTypeArguments typeArgs
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
        validTypeNameE <*>
        fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeTypeArgumentsE
  return $ crtwE

getValidTypeParams :: [Parameter] -> StateT ClassData IO (Val.Validation [TypeError] [ValidTypeParameter])
getValidTypeParams = 
  foldrM (\(NewParameter tp@(ClassType pos qn typeArgs) nmpos nm) accum -> do
    vtqnE <- validateM [TypeError ("Undefined type: "++show tp) pos] getValidTypeQualifiedName qn
    validTypeTypeArgumentsE <- mapValidTypeTypeArguments typeArgs
    let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
          vtqnE <*>
          fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeTypeArgumentsE
    let vtpE = ValidTypeParameter (nm,nmpos) <$> crtwE
    return $ (:) <$> vtpE <*> accum)
  (Val.Success [])
    
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
getValidTypeTerm (Value (ObjectCreation pos (ClassType tppos tp typeArgs) args)) = do
  validTypeNameE <- validateM [TypeError ("Undefined type: "++show tp) pos] getValidTypeQualifiedName tp
  validTypeArgumentsE <- getTermValidTypeArguments args
  validTypeTypeArgumentsE <- mapValidTypeTypeArguments typeArgs
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
        validTypeNameE <*>
        fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeTypeArgumentsE
  let vtocE = ValidTypeObjectCreation pos <$> crtwE <*> validTypeArgumentsE
  return $ ValidTypeValue <$> vtocE
getValidTypeTerm (Value (ObjectCreation pos (TypeVariable tppos tpvar) args)) = undefined
getValidTypeTerm (Cast (ClassType pos tp typeArgs) term) = do
  validTypeNameE <- validateM [TypeError ("Undefined type: "++show tp) pos] getValidTypeQualifiedName tp
  validTypeTermE <- getValidTypeTerm term
  validTypeTypeArgumentsE <- mapValidTypeTypeArguments typeArgs
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
        validTypeNameE <*>
        fmap (\args -> case args of [] -> Nothing; as -> Just (V.fromList as)) validTypeTypeArgumentsE
  let vtrtdE = ValidTypeRefTypeDeclaration pos <$> crtwE
  return $ ValidTypeCast <$> vtrtdE <*> validTypeTermE
getValidTypeTerm (Cast (TypeVariable pos tpvar) term) = undefined
getValidTypeTerm (Application (ApplicationTargetTerm t) (FieldAccess pos nm)) = do
  validTypeTermE <- getValidTypeTerm t
  return $ 
    ValidTypeApplication <$>
      (ValidTypeApplicationTargetTerm <$> validTypeTermE) <*>
      pure (ValidTypeFieldAccess pos nm)
getValidTypeTerm (Application (ApplicationTargetTerm t) (MethodInvocation pos nm args)) = do
  validTypeTermE <- getValidTypeTerm t
  validTypeArgsE <- getTermValidTypeArguments args
  let att = ValidTypeApplicationTargetTerm <$> validTypeTermE
  let mi = ValidTypeMethodInvocation pos nm <$> validTypeArgsE
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
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$> validTypeNameE <*> pure Nothing
  let rtdE = ValidTypeRefTypeDeclaration tppos <$> crtwE
  let attnE = ValidTypeApplicationTargetTypeName <$> rtdE
  return $ ValidTypeApplication <$> attnE <*> pure (ValidTypeFieldAccess pos nm)
getValidTypeTerm (Application (ApplicationTargetTypeName (TypeVariable tppos tpvar)) (FieldAccess pos nm)) = undefined
getValidTypeTerm (Application (ApplicationTargetTypeName (ClassType tppos tp _)) (MethodInvocation pos nm args)) = do
  vtqnE <- validateM [TypeError "Type not valid in this context" tppos] getValidTypeQualifiedName tp
  validTypeArgsE <- getTermValidTypeArguments args
  let crtwE = TypeCheckerClassReferenceTypeWrapper <$>
        vtqnE <*>
        pure Nothing
  let vmiE = ValidTypeMethodInvocation pos nm <$> validTypeArgsE
  let vtrtdE = ValidTypeRefTypeDeclaration tppos <$> crtwE
  let vtattnE = ValidTypeApplicationTargetTypeName <$> vtrtdE
  return $
    ValidTypeApplication <$> vtattnE <*> vmiE
getValidTypeTerm (Application (ApplicationTargetTypeName (ClassType tppos tp _)) (SuperMethodInvocation pos nm args)) = undefined

getValidTypeTerm (Application (ApplicationTargetTypeName (TypeVariable tppos tpvar)) (MethodInvocation pos nm params)) = undefined
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