{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

{-- Parse a stream of tokens into a Map of Clazz's. Each Clazz has Fields, Constructors and Methods that contain tokens. -}

module Parser
  ( satisfy
  , satisfyAny
  , satisfySimpleName
  , satisfyQualifiedName
  , createName
  , createQName
  , createNameThis
  , createNameSuper
  , createNameInit
  , simpleNameToString
  , createQNameObject
  , createQNameInteger
  , createQNameString
  , createQNameBoolean
  , deconstructQualifiedName
  , deconstructSimpleName
  , constructQualifiedName
  , constructSimpleName
  , ClassAccessFlag(..)
  , MethodAccessFlag(..)
  , Clazz(NewClazz)
  , Field(NewField)
  , Constructor(NewConstructor)
  , Method(NewMethod)
  , Body(..)
  , QualifiedName
  , SimpleName
  , CompilationUnit(..)
  , parseCompilationUnit
  , NameToPackageMap
  ) where

import Data.Functor.Identity (Identity)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Data.Maybe ( fromMaybe )
import Text.Parsec.Prim
import Text.Parsec.Combinator
    ( anyToken, eof, manyTill, optionMaybe )
import Text.Parsec.Pos
import Text.Parsec.Error ( ParseError, newErrorMessage, Message (Message) )
import Lexer
import ClassPath ( ClassPath, getPackageClasses )
import TypeCheckerTypes
import Debug.Trace
import qualified Data.Map.Merge.Strict as Map

type NameToPackageMap = Map.Map T.Text [T.Text] -- Mapping from an unqualified name to a package

data Import = SingleTypeImport SourcePos [T.Text] T.Text | TypeImportOnDemand SourcePos [T.Text] deriving Show

data Body = NewBody [TokenPos] | EmptyBody deriving Show

data Constructor = NewConstructor SourcePos [TokenPos] Body deriving Show

data Field = NewField [TokenPos] [TokenPos] TokenPos deriving Show -- Type TypeArgs Name

data Method = NewMethod [MethodAccessFlag] [TokenPos] TokenPos [TokenPos] Body deriving Show

data Clazz = NewClazz SourcePos CompilationUnit QualifiedName [ClassAccessFlag] (Maybe [TokenPos]) [Field] [Constructor] [Method] deriving Show

data ClazzMember = ConstructorMember Constructor | FieldMember Field | MethodMember Method deriving Show

data CompilationUnit = CompilationUnit {classpath :: ClassPath, package :: [T.Text], imports :: NameToPackageMap, types :: [Clazz]} deriving Show

sep = T.singleton '/'

parseCompilationUnit :: ClassPath -> NameToPackageMap -> [TokenPos] -> Either ParseError [Clazz]
parseCompilationUnit cp defaultNameMapping toks = do
  (package, toks') <- runParser packageDeclaration () "" toks
  (importDeclarationsList, toks'') <- runParser importDeclarationList () "" toks'
  simpleNameToPackageMap <- createSimpleNameToPackageMap cp defaultNameMapping importDeclarationsList
  parseTypeDeclarations toks'' (CompilationUnit {classpath=cp, package=package, imports=simpleNameToPackageMap, types=[]})

parseTypeDeclarations ::  [TokenPos] -> CompilationUnit -> Either ParseError [Clazz]
parseTypeDeclarations [] CompilationUnit {..} = Right types
parseTypeDeclarations toks compUnit = do
  (compUnit',toks') <- parseClass toks compUnit
  parseTypeDeclarations toks' compUnit'

parseClass :: [TokenPos] -> CompilationUnit -> Either ParseError (CompilationUnit, [TokenPos])
parseClass toks compUnit = runParser clazzDeclaration compUnit "" toks

packageDeclaration :: (Stream s Identity (Token, SourcePos)) => Parsec s u ([T.Text], [TokenPos])
packageDeclaration = do
  maybePackage <- optionMaybe (satisfyKeyword "package")
  case maybePackage of
    Just p -> do
      toks <- satisfyQualifiedName
      satisfy Semi;
      rest <- manyTill anyToken eof
      return (fmap (\(Ide t,pos) -> t) (filter (\(tk,pos) -> case tk of Ide _ -> True; _ -> False) toks), rest)
    Nothing -> do
      rest <- manyTill anyToken eof
      return ([],rest)

importDeclarationList :: (Stream s Identity (Token, SourcePos)) => Parsec s u ([Import], [TokenPos])
importDeclarationList = do
  importList <- importDeclarationList'
  rest <- manyTill anyToken eof
  return (importList, rest)

importDeclarationList' :: (Stream s Identity (Token, SourcePos)) => Parsec s u [Import]
importDeclarationList' = do
  maybeImport <- optionMaybe importDeclaration
  case maybeImport of
    Just i -> do
      importList <- importDeclarationList'
      return $ i:importList
    Nothing -> return []

importDeclaration :: (Stream s Identity (Token, SourcePos)) => Parsec s u Import
importDeclaration = do
  satisfyKeyword "import"
  typeNameTokens <- satisfyPackageOrTypeName
  satisfy Semi;
  let (_, pos) = head typeNameTokens
  let (lastToken, _) = last typeNameTokens
  case lastToken of
    Asterick -> return $ TypeImportOnDemand pos (stripTokenText typeNameTokens) -- stripTokenText strips asterick also
    _ -> return $ SingleTypeImport pos (init (stripTokenText typeNameTokens)) (last (stripTokenText typeNameTokens))

stripTokenText :: [TokenPos] -> [T.Text]
stripTokenText toks = fmap (\(Ide t,_) -> t) (filter (\(tk,_) -> case tk of Ide _ -> True; _ -> False) toks)

createSimpleNameToPackageMap :: ClassPath -> NameToPackageMap -> [Import] -> Either ParseError NameToPackageMap
createSimpleNameToPackageMap cp defaultNameMapping importList =
  Map.union defaultNameMapping . Map.fromList . concat <$> sequence (foldl (\l i -> mapImportToNamePackagePairs cp i:l) [] importList)

mapImportToNamePackagePairs :: ClassPath -> Import -> Either ParseError [(T.Text, [T.Text])]
mapImportToNamePackagePairs cp (SingleTypeImport pos package name) =
  case getPackageClasses cp package of
    Nothing -> Left $ newErrorMessage (Message "Unknown package") pos
    Just nameList ->
      if name `elem` nameList then Right [(name, package)] else Left $ newErrorMessage (Message "Unknown name") pos
mapImportToNamePackagePairs cp (TypeImportOnDemand pos package) =
  case getPackageClasses cp package of
    Nothing -> Left $ newErrorMessage (Message "Unkown package") pos
    Just txts -> Right (fmap (, package) txts)

clazzClause :: (Stream s Identity (Token, SourcePos)) => Parsec s u (SimpleName, SourcePos)
clazzClause = do
  satisfyKeyword "class"
  (name,pos) <- satisfySimpleNameText
  return (SimpleName name, pos)

extendsClause :: (Stream s Identity (Token, SourcePos)) => Parsec s u [TokenPos]
extendsClause = do
  satisfyKeyword "extends"
  satisfyQualifiedName

fieldDeclaration :: (Stream s Identity (Token, SourcePos)) => Parsec s u ClazzMember
fieldDeclaration = do
  tp <- satisfyQualifiedName
  maybeTypeArguments <- optionMaybe typeArgumentList
  name <- satisfySimpleName
  satisfy Semi
  return $ FieldMember (NewField tp (fromMaybe [] maybeTypeArguments) name)

parameterList :: (Stream s Identity TokenPos) => Parsec s u [TokenPos]
parameterList = do
  satisfy LParens
  manyTill anyToken (try (satisfy RParens))

typeArgumentList :: (Stream s Identity TokenPos) => Parsec s u [TokenPos]
typeArgumentList = do
  satisfy LAngleBracket
  manyTill anyToken (try (satisfy RAngleBracket))

constructorDeclaration :: (Stream s Identity (Token, SourcePos)) => T.Text -> Parsec s u ClazzMember
constructorDeclaration className = do
  pos <- token (\(tok, pos) -> show tok) snd (\(tok, pos) -> case tok of (Ide nm) | nm == className -> Just pos; _ -> Nothing)
  params <- parameterList
  ConstructorMember . NewConstructor pos params <$> methodBody

methodDeclaration :: (Stream s Identity (Token, SourcePos)) => Parsec s u ClazzMember
methodDeclaration = do
  abs <- try $ optionMaybe $ satisfyKeyword "abstract"
  tp <- satisfyQualifiedName
  name <- satisfySimpleName
  params <- parameterList
  case abs of
    Just _ -> do
      satisfy Semi;
      return ((MethodMember . NewMethod [MAbstract] tp name params) EmptyBody)
    Nothing -> MethodMember . NewMethod [] tp name params <$> methodBody

methodBody :: (Stream s Identity (Token, SourcePos)) => Parsec s u Body
methodBody = do
  satisfy LBrace
  terms <- manyTill anyToken (try (satisfy RBrace))
  return (NewBody terms)

classMemberDeclarations :: (Stream s Identity (Token, SourcePos)) => T.Text -> Parsec s u [ClazzMember]
classMemberDeclarations clazzName = do
  maybeMember <- optionMaybe (try fieldDeclaration <|> try (constructorDeclaration clazzName) <|> try methodDeclaration)
  case maybeMember of
    Just member -> fmap ([member] ++) (classMemberDeclarations clazzName)
    Nothing -> return []

clazzDeclaration :: (Stream s Identity (Token, SourcePos)) => Parsec s CompilationUnit (CompilationUnit, [(Token, SourcePos)])
clazzDeclaration = do
  cu@CompilationUnit {..} <- getState
  maybeAbstract <- try $ optionMaybe $ satisfyKeyword "abstract"
  (clazz@(SimpleName clazzName), pos) <- clazzClause
  maybeSuperClazz <- optionMaybe extendsClause
  satisfy LBrace
  clazzMembers <- classMemberDeclarations clazzName
  satisfy RBrace
  rest <- manyTill anyToken eof
  let af = case maybeAbstract of Just _ -> [CAbstract]; Nothing -> []
  let newClazz = NewClazz
                   pos cu (QualifiedName package clazz) af maybeSuperClazz
                   (extractField <$> filter (\case (FieldMember _) -> True; _ -> False) clazzMembers)
                   (extractConstructor <$> filter (\case (ConstructorMember _) -> True; _ -> False) clazzMembers)
                   (extractMethod <$> filter (\case (MethodMember _) -> True; _ -> False) clazzMembers)
                   where extractField (FieldMember f) = f
                         extractConstructor (ConstructorMember c) = c
                         extractMethod (MethodMember m) = m
  return (CompilationUnit {types=newClazz:types, ..}, rest)

satisfyAny :: (Stream s Identity (Token, SourcePos)) => Parsec s u (SourcePos,Token)
satisfyAny = token (\(tok, pos) -> show tok)
                  snd
                  (\(tok, pos) -> Just (pos,tok))

satisfy :: (Stream s Identity (Token, SourcePos)) => Token -> Parsec s u SourcePos
satisfy t = token (\(tok, pos) -> show tok)
                  snd
                  (\(tok, pos) -> if tok == t then Just pos else Nothing)

satisfyKeyword :: (Stream s Identity (Token, SourcePos)) => String -> Parsec s u SourcePos
satisfyKeyword k = token (\(tok, pos) -> show tok)
                         snd
                         (\(tok, pos) -> case tok of Keyword k' -> if k == k' then Just pos else Nothing; _ -> Nothing)

satisfySimpleNameText :: (Stream s Identity (Token, SourcePos)) => Parsec s u (T.Text, SourcePos)
satisfySimpleNameText = token (\(tok, pos) -> show tok)
                         snd
                         (\(tok, pos) -> case tok of Ide s -> Just (s,pos); _ -> Nothing)

satisfySimpleName :: (Stream s Identity (Token, SourcePos)) => Parsec s u TokenPos
satisfySimpleName = token (\(tok, pos) -> show tok)
                          snd
                          (\(tok, pos) -> case tok of Ide _ -> Just (tok,pos); _ -> Nothing)

satisfyQualifiedName :: (Stream s Identity TokenPos) => Parsec s u [TokenPos]
satisfyQualifiedName = do
  first <- satisfySimpleName
  satisfyQualifiedName' [first]

satisfyQualifiedName' :: (Stream s Identity TokenPos) => [TokenPos] -> Parsec s u [TokenPos]
satisfyQualifiedName' first = do
  maybeDot <- optionMaybe (satisfy Dot)
  case maybeDot of
    Just dotpos -> do
      next <- satisfySimpleName
      satisfyQualifiedName' (next:((Dot,dotpos):first))
    Nothing -> return (reverse first)

satisfyPackageOrTypeName :: (Stream s Identity TokenPos) => Parsec s u [TokenPos]
satisfyPackageOrTypeName = do
  first <- satisfySimpleName
  satisfyPackageOrTypeName' [first]

satisfyPackageOrTypeName' :: (Stream s Identity TokenPos) => [TokenPos] -> Parsec s u [TokenPos]
satisfyPackageOrTypeName' first = do
  maybeDot <- optionMaybe (satisfy Dot)
  case maybeDot of
    Just dotpos -> do
      maybeAsterick <- optionMaybe (satisfy Asterick)
      case maybeAsterick of
        Just asterickPos ->
          satisfyPackageOrTypeName' ((Asterick,asterickPos):((Dot,dotpos):first))
        Nothing -> do
          next <- satisfySimpleName
          satisfyPackageOrTypeName' (next:((Dot,dotpos):first))
    Nothing -> return (reverse first)

createName :: TokenPos -> (SimpleName, SourcePos)
createName (Ide name, pos) = (SimpleName name, pos)

createNameThis = SimpleName (T.pack "this")

createNameSuper = SimpleName (T.pack "super")

createNameInit = SimpleName (T.pack "<init>")

{-- Create a qualified name from a list of tokens. If the list of tokens has only 1 token, apply the package and lookup
    the token name in the imports -}
createQName :: [T.Text] -> Map.Map QualifiedName Clazz -> NameToPackageMap -> [TokenPos] -> (QualifiedName, SourcePos)
createQName package classMap imports [(tok,pos)]
  | Map.member qn classMap =
  (qn, pos)
  | Map.member sn imports =
  (QualifiedName (imports Map.! sn) (SimpleName sn), pos)
  | otherwise =
  (QualifiedName [] (SimpleName sn), pos)
  where
    (Ide sn) = tok
    qn = QualifiedName package (SimpleName sn)
createQName package classMap imports toks =
  (qn, pos)
  where ts = foldl (\ts tok -> case tok of (Ide t,_) -> t:ts; _ -> trace (show tok) undefined) [] toks
        q = init ts
        n = last ts
        qn = QualifiedName q (SimpleName n)
        (_,pos) = head toks


simpleNameToString (SimpleName name) = T.unpack name