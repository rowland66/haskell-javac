{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

{-- Parse a stream of tokens into a Map of Clazz's. Each Clazz has Fields, Constructors and Methods, that contain  -}
module Parser
  ( satisfy
  , satisfySimpleName
  , satisfyQualifiedName
  , createName
  , createQName
  , createNameThis
  , createNameInit
  , simpleNameToString
  , createQNameObject
  , deconstructQualifiedName
  , Clazz(NewClazz)
  , Field(NewField)
  , Constructor(NewConstructor)
  , Method(NewMethod)
  , Body(NewBody)
  , QualifiedName
  , SimpleName
  , parseCompilationUnit
  ) where

import Data.Functor.Identity (Identity)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.Parsec.Pos
import Text.Parsec.Error
import Lexer
import Debug.Trace


data Body = NewBody [(Token, SourcePos)] deriving Show

data Constructor = NewConstructor SourcePos [TokenPos] Body deriving Show

data Field = NewField [TokenPos] deriving Show

data Method = NewMethod [TokenPos] TokenPos [TokenPos] Body deriving Show

data Clazz = NewClazz SourcePos [T.Text] [[TokenPos]] QualifiedName (Maybe [TokenPos]) [Field] [Constructor] [Method] deriving Show

data ClazzMember = ConstructorMember Constructor | FieldMember Field | MethodMember Method deriving Show

data CompilationUnit = CompilationUnit {package :: [T.Text], imports :: [[TokenPos]], types :: [Clazz]}

data QualifiedName = QualifiedName [T.Text] SimpleName deriving (Eq, Ord)

newtype SimpleName = SimpleName T.Text deriving (Eq, Ord)

instance Show SimpleName where
  show (SimpleName n) = T.unpack n

instance Show QualifiedName where
  show (QualifiedName [] n) = show n
  show (QualifiedName p (SimpleName n)) = T.unpack $ T.concat ((T.intercalate sep p):sep:n:[])

sep = T.singleton '/'

parseCompilationUnit :: [TokenPos] -> (Either ParseError [Clazz])
parseCompilationUnit toks = do
  (package, toks') <- runParser packageDeclaration () "" toks
  importDeclarationList <- return []
  trace "parse" $ parseTypeDeclarations toks' (CompilationUnit {package=package, imports=importDeclarationList, types=[]})

parseTypeDeclarations ::  [TokenPos] -> CompilationUnit -> (Either ParseError [Clazz])
parseTypeDeclarations [] (CompilationUnit {..}) = Right types
parseTypeDeclarations toks compUnit = do
  (compUnit',toks') <- parseClass toks compUnit
  parseTypeDeclarations toks' compUnit'

parseClass :: [TokenPos] -> CompilationUnit -> (Either ParseError (CompilationUnit, [TokenPos]))
parseClass toks compUnit = runParser clazzDeclaration compUnit "" toks

packageDeclaration :: (Stream s Identity (Token, SourcePos)) => Parsec s u ([T.Text], [TokenPos])
packageDeclaration = do
  maybePackage <- optionMaybe (satisfyKeyword "package")
  case maybePackage of
    Just p -> do
      toks <- trace "package found" $ satisfyQualifiedName
      trace (show toks) $ satisfy Semi;
      rest <- manyTill anyToken eof
      return ((fmap (\((Ide t),pos) -> t) (filter (\(tk,pos) -> case tk of Ide _ -> True; _ -> False) toks)), rest)
    Nothing -> do
      rest <- manyTill anyToken eof
      return ([],rest)

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
  name <- satisfySimpleName
  satisfy Semi
  return $ FieldMember (NewField (tp++[name]))

parameterList :: (Stream s Identity TokenPos) => Parsec s u [TokenPos]
parameterList = do
  satisfy LParens
  manyTill anyToken (try (satisfy RParens))

constructorDeclaration :: (Stream s Identity (Token, SourcePos)) => T.Text -> Parsec s u ClazzMember
constructorDeclaration className = do
  pos <- token (\(tok, pos) -> (show tok)) (\(tok, pos) -> pos) (\(tok, pos) -> case tok of (Ide className) -> Just pos; _ -> Nothing)
  params <- parameterList
  body <- methodBody
  return $ ConstructorMember (NewConstructor pos params body)

methodDeclaration :: (Stream s Identity (Token, SourcePos)) => Parsec s u ClazzMember
methodDeclaration = do
  tp <- satisfyQualifiedName
  name <- satisfySimpleName
  params <- parameterList
  body <- methodBody
  return $ MethodMember $ NewMethod tp name params body

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
  (CompilationUnit {..}) <- getState
  (clazz@(SimpleName clazzName), pos) <- clazzClause
  {--if (Map.member clazzName clazzMap) then (parserFail ("Duplicate class " ++ clazzName)) else parserReturn ()-}
  maybeSuperClazz <- optionMaybe extendsClause
  satisfy LBrace
  clazzMembers <- classMemberDeclarations clazzName
  satisfy RBrace
  rest <- manyTill anyToken eof
  let newClazz = (NewClazz
                   pos package imports (QualifiedName package clazz) maybeSuperClazz
                   (fmap extractField $ filter (\m -> case m of (FieldMember _) -> True; (_) -> False) clazzMembers)
                   (fmap extractConstructor $ filter (\m -> case m of (ConstructorMember _) -> True; (_) -> False) clazzMembers)
                   (fmap extractMethod $ filter (\m -> case m of (MethodMember _) -> True; (_) -> False) clazzMembers))
                   where extractField (FieldMember f) = f
                         extractConstructor (ConstructorMember c) = c
                         extractMethod (MethodMember m) = m
  return (CompilationUnit {types=(newClazz:types), ..}, rest)

satisfy :: (Stream s Identity (Token, SourcePos)) => Token -> Parsec s u SourcePos
satisfy t = token (\(tok, pos) -> (show tok))
                  (\(tok, pos) -> pos)
                  (\(tok, pos) -> if tok == t then Just pos else Nothing)

satisfyKeyword :: (Stream s Identity (Token, SourcePos)) => String -> Parsec s u SourcePos
satisfyKeyword k = token (\(tok, pos) -> (show tok))
                         (\(tok, pos) -> pos)
                         (\(tok, pos) -> case tok of Keyword k' -> if (k == k') then Just pos else Nothing; _ -> Nothing)

satisfySimpleNameText :: (Stream s Identity (Token, SourcePos)) => Parsec s u (T.Text, SourcePos)
satisfySimpleNameText = token (\(tok, pos) -> (show tok))
                         (\(tok, pos) -> pos)
                         (\(tok, pos) -> case tok of Ide s -> Just (s,pos); _ -> Nothing)

satisfySimpleName :: (Stream s Identity (Token, SourcePos)) => Parsec s u TokenPos
satisfySimpleName = token (\(tok, pos) -> (show tok))
                          (\(tok, pos) -> pos)
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

createName :: TokenPos -> (SimpleName, SourcePos)
createName ((Ide name), pos) = (SimpleName name, pos)

createNameThis = SimpleName (T.pack "this")

createNameInit = SimpleName (T.pack "<init>")

createQName :: [T.Text] -> [TokenPos] -> (QualifiedName, SourcePos)
createQName package toks =
  ((QualifiedName q (SimpleName n)), pos)
  where ts = foldl (\ts ((Ide t),_) -> t:ts) [] toks
        q = if ((length ts) == 1) then package else (init ts)
        n = if ((length ts) == 1) then (head ts) else (last ts)
        (_,pos) = head toks

simpleNameToString (SimpleName name) = T.unpack name

createQNameObject = QualifiedName ((T.pack "java"):(T.pack "lang"):[]) (SimpleName (T.pack "Object"))

deconstructQualifiedName :: QualifiedName -> ([T.Text], T.Text)
deconstructQualifiedName (QualifiedName p (SimpleName n)) = (p,n)
