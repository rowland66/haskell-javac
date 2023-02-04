{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

module TypeCheckerTypes
  ( SimpleName (..)
  , QualifiedName (..)
  , IValidTypeName (..)
  , IValidTypeReferenceType (..)
  , IValidTypeReferenceTypeWrapper(..)
  , IValidTypeTypeArgument(..)
  {--, ValidTypeReferenceType(..) -}
  , ValidTypeWildcardIndicator(..)
  , createQNameObject
  , createQNameInteger
  , createQNameString
  , createQNameBoolean
  , constructSimpleName
  , constructQualifiedName
  , deconstructSimpleName
  , deconstructQualifiedName
  , ClassAccessFlag(..)
  , MethodAccessFlag(..)
  , FieldAccessFlag(..)
  )
where

import Data.Int
import qualified Data.Text as T
import Text.Parsec.Pos ( SourcePos )
import TextShow

data QualifiedName = QualifiedName [T.Text] SimpleName deriving (Eq, Ord)

class IValidTypeReferenceType a where
  getValidTypeRefTypeTypeName :: a -> QualifiedName

data IValidTypeReferenceTypeWrapper = forall a. IValidTypeReferenceType a => IValidTypeReferenceTypeWrapper a

class IValidTypeName a where
  getValidTypeQName :: a -> QualifiedName

class IValidTypeTypeArgument a where
  isExtends :: a -> Bool
  isSuper :: a -> Bool
  getTypeArgumentType :: a -> IValidTypeReferenceTypeWrapper

{--
data ValidTypeTypeArgument = forall b. IValidTypeReferenceType b => 
  ValidTypeTypeArgument { getValidTypeArgumentWildcard :: Maybe ValidTypeWildcardIndicator
                        , getValidTypeArgumentValidType :: b
                        }

data ValidTypeReferenceType = forall b. (ValidType b, Show b) =>
    ClassReferenceType { getReferenceTypeClassValidType :: b }
  | TypeVariableReferenceType { getReferenceTypeTypeVariable :: SimpleName
  }

instance Show ValidTypeReferenceType where
  show (ClassReferenceType tcvt) = "ClassReferenceType "++show tcvt
  show (TypeVariableReferenceType sn) = "TypeVariableReferenceType "++show sn
  -}
data ValidTypeWildcardIndicator = ValidTypeWildcardIndicatorExtends | ValidTypeWildcardIndicatorSuper deriving (Show, Eq)

newtype SimpleName = SimpleName T.Text deriving (Eq, Ord)

instance Show SimpleName where
  show sn = T.unpack (toText (showb sn))

instance TextShow SimpleName where
  showb (SimpleName n) = fromText n

instance Show QualifiedName where
  show (QualifiedName [] n) = show n
  show (QualifiedName p (SimpleName n)) = T.unpack $ T.concat [T.intercalate sep p, sep, n]

instance TextShow QualifiedName where
  showb (QualifiedName [] sn) = showb sn
  showb (QualifiedName p (SimpleName n)) = fromText $ T.concat [T.intercalate sep p, sep, n]

sep = T.singleton '/'

createQNameObject = QualifiedName [T.pack "java", T.pack "lang"] (SimpleName (T.pack "Object"))

createQNameInteger = QualifiedName [T.pack "java", T.pack "lang"] (SimpleName (T.pack "Integer"))

createQNameString = QualifiedName [T.pack "java", T.pack "lang"] (SimpleName (T.pack "String"))

createQNameBoolean = QualifiedName [T.pack "java", T.pack "lang"] (SimpleName (T.pack "Boolean"))

deconstructSimpleName :: SimpleName -> T.Text
deconstructSimpleName (SimpleName n) = n

deconstructQualifiedName :: QualifiedName -> ([T.Text], T.Text)
deconstructQualifiedName (QualifiedName p (SimpleName n)) = (p, n)

constructQualifiedName :: T.Text -> QualifiedName
constructQualifiedName t =
  let (package, simpleName) = T.breakOnEnd sep t
   in QualifiedName (T.splitOn sep (T.dropEnd 1 package)) (SimpleName simpleName)

constructSimpleName :: T.Text -> SimpleName
constructSimpleName = SimpleName

data ClassAccessFlag = CPublic | CInterface | CAbstract deriving (Enum, Eq, Show)

data FieldAccessFlag = FStatic deriving (Enum, Eq, Show)

data MethodAccessFlag = MStatic | MAbstract | MSynthetic | MBridge deriving (Enum, Eq, Show)

{-- Unused parameterized type below -}
data Abstraction_ n
  = FieldAccess_ SourcePos SimpleName
  | MethodInvocation_ SourcePos Bool SimpleName [Term_ n]
  deriving (Show)

data TypeName_ n = TypeName_ SourcePos n deriving (Show)

data Value_ n
  = Variable_ SourcePos SimpleName
  | IntegerLit_ SourcePos Int32
  | StringLit_ SourcePos String
  | BooleanLit_ SourcePos Bool
  | ObjectCreation_ SourcePos n [Term_ n]
  deriving (Show)

data ApplicationTarget_ n
  = ApplicationTargetTerm_ (Term_ n)
  | ApplicationTargetTypeName_ (TypeName_ n)
  deriving (Show)

data Term_ n
  = Value_ (Value_ n)
  | Application_ (ApplicationTarget_ n) (Abstraction_ n)
  | Conditional_ (Term_ n) (Term_ n) (Term_ n)
  | Cast_ (TypeName_ n) (Term_ n)
  deriving (Show)

data Parameter_ n = Parameter_
  { vpName :: (SimpleName, SourcePos),
    vpType :: n
  }
  deriving (Show, Eq)

data ConstructorInvocation_ n = ConstructorInvocation_ SourcePos [Term_ n] deriving (Show)

data SuperConstructorInvocation_ n = SuperConstructorInvocation_ SourcePos [Term_ n] deriving (Show)

data Assignment_ n = Assignment_
  { vaRightHandTerm :: Term_ n,
    vaLeftHandTerm :: Term_ n
  }
  deriving (Show)

data MethodImplementation_ n
  = MethodImplementation_ {vmiTerm :: Term_ n}
  | ConstructorImplementation_
      { vmiConstructorInvocation :: Either (ConstructorInvocation_ n) (SuperConstructorInvocation_ n),
        vmiAssignments :: [Assignment_ n]
      }
  deriving (Show)

data Field_ n = Field_
  { vfName :: (SimpleName, SourcePos),
    vfType :: n
  }
  deriving (Show)

data Method_ n = Method_
  { vmName :: (SimpleName, SourcePos),
    vmAccessFlags :: [MethodAccessFlag],
    vmType :: n,
    vmParams :: [Parameter_ n],
    vmMaybeImpl :: Maybe (MethodImplementation_ n)
  }
  deriving (Show)

data Clazz_ n = ValidTypeClazz_
  { vcAccessFlags :: [ClassAccessFlag],
    vcName :: n,
    vcSourcePos :: SourcePos,
    vcParent :: (n, SourcePos),
    vcFields :: [Field_ n],
    vcMethods :: [Method_ n]
  }
  deriving (Show)
