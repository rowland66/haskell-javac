{-# LANGUAGE FlexibleContexts #-}

module Parser
  ( satisfy
  , satisfyIde
  , Clazz(NewClazz)
  , Field(NewField)
  , Constructor(NewConstructor)
  , Method(NewMethod)
  , Body(NewBody)
  , parseClasses
  ) where

import Data.Functor.Identity (Identity)
import qualified Data.Map.Strict as Map
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

data Clazz = NewClazz SourcePos String (Maybe TokenPos) [Field] [Constructor] [Method] deriving Show

data ClazzMember = ConstructorMember Constructor | FieldMember Field | MethodMember Method deriving Show

parseClasses :: [TokenPos] -> (Either ParseError (Map.Map String Clazz))
parseClasses toks = trace "Parser1" $ parseClasses' toks Map.empty

parseClasses' :: [TokenPos] -> Map.Map String Clazz -> (Either ParseError (Map.Map String Clazz))
parseClasses' [] types = (Right types)
parseClasses' toks types = do
  (types',toks') <- parseClass toks types
  parseClasses' toks' types'

parseClass :: [TokenPos] -> Map.Map String Clazz -> (Either ParseError (Map.Map String Clazz, [TokenPos]))
parseClass toks types = let rtrn = runParser clazzDeclaration types "" toks in rtrn

clazzClause :: (Stream s Identity (Token, SourcePos)) => Parsec s u (SourcePos, String)
clazzClause = do
  token (\(tok, pos) -> (show tok)) (\(tok, pos) -> pos) (\(tok, pos) -> case tok of Keyword "class" -> Just ""; _ -> Nothing)
  (pos,name) <- token (\(tok, pos) -> (show tok)) (\(tok, pos) -> pos) (\(tok, pos) -> case tok of Ide i -> Just (pos,i); _ -> Nothing)
  return (pos,name)

extendsClause :: (Stream s Identity (Token, SourcePos)) => Parsec s u TokenPos
extendsClause = do
  token (\(tok, pos) -> (show tok)) (\(tok, pos) -> pos) (\(tok, pos) -> case tok of Keyword "extends" -> Just ""; _ -> Nothing)
  name <- token (\(tok, pos) -> (show tok)) (\(tok, pos) -> pos) (\(tok, pos) -> case tok of Ide i -> Just (tok,pos); _ -> Nothing)
  return name

fieldDeclaration :: (Stream s Identity (Token, SourcePos)) => Parsec s u ClazzMember
fieldDeclaration = do
  tp <- satisfyTypeIde
  name <- satisfyIde
  satisfy Semi
  return $ FieldMember (NewField (tp++[name]))

parameterList :: (Stream s Identity TokenPos) => Parsec s u [TokenPos]
parameterList = do
  satisfy LParens
  manyTill anyToken (try (satisfy RParens))

constructorDeclaration :: (Stream s Identity (Token, SourcePos)) => String -> Parsec s u ClazzMember
constructorDeclaration className = do
  pos <- token (\(tok, pos) -> (show tok)) (\(tok, pos) -> pos) (\(tok, pos) -> case tok of (Ide className) -> Just pos; _ -> Nothing)
  params <- parameterList
  body <- methodBody
  return $ ConstructorMember (NewConstructor pos params body)

methodDeclaration :: (Stream s Identity (Token, SourcePos)) => Parsec s u ClazzMember
methodDeclaration = do
  tp <- satisfyTypeIde
  name <- satisfyIde
  params <- parameterList
  body <- methodBody
  return $ MethodMember $ NewMethod tp name params body

methodBody :: (Stream s Identity (Token, SourcePos)) => Parsec s u Body
methodBody = do
  satisfy LBrace
  terms <- manyTill anyToken (try (satisfy RBrace))
  return (NewBody terms)

classMemberDeclarations :: (Stream s Identity (Token, SourcePos)) => String -> Parsec s u [ClazzMember]
classMemberDeclarations clazzName = do
  maybeMember <- optionMaybe (try fieldDeclaration <|> try (constructorDeclaration clazzName) <|> try methodDeclaration)
  case maybeMember of
    Just member -> fmap ([member] ++) (classMemberDeclarations clazzName)
    Nothing -> return []

clazzDeclaration :: (Stream s Identity (Token, SourcePos)) => Parsec s (Map.Map String Clazz) (Map.Map String Clazz, [(Token, SourcePos)])
clazzDeclaration = do
  clazzMap <- getState
  (pos,clazzName) <- clazzClause
  if (Map.member clazzName clazzMap) then (parserFail ("Duplicate class " ++ clazzName)) else parserReturn ()
  superClazz <- optionMaybe extendsClause
  token (\(tok, pos) -> (show tok)) (\(tok, pos) -> pos) (\(tok, pos) -> case tok of LBrace -> Just (); _ -> Nothing)
  clazzMembers <- classMemberDeclarations clazzName
  token (\(tok, pos) -> (show tok)) (\(tok, pos) -> pos) (\(tok, pos) -> case tok of RBrace -> Just (); _ -> Nothing)
  rest <- manyTill anyToken eof
  return (Map.insert clazzName (NewClazz
    pos clazzName superClazz
    (fmap extractField $ filter (\m -> case m of (FieldMember _) -> True; (_) -> False) clazzMembers)
    (fmap extractConstructor $ filter (\m -> case m of (ConstructorMember _) -> True; (_) -> False) clazzMembers)
    (fmap extractMethod $ filter (\m -> case m of (MethodMember _) -> True; (_) -> False) clazzMembers)) clazzMap, rest)
    where extractField (FieldMember f) = f
          extractConstructor (ConstructorMember c) = c
          extractMethod (MethodMember m) = m

satisfy :: (Stream s Identity (Token, SourcePos)) => Token -> Parsec s u SourcePos
satisfy t = token (\(tok, pos) -> (show tok))
                  (\(tok, pos) -> pos)
                  (\(tok, pos) -> if tok == t then Just (pos) else Nothing)

satisfyIde :: (Stream s Identity (Token, SourcePos)) => Parsec s u TokenPos
satisfyIde = token (\(tok, pos) -> (show tok))
                  (\(tok, pos) -> pos)
                  (\(tok, pos) -> case tok of Ide _ -> Just (tok,pos); _ -> Nothing)

satisfyTypeIde :: (Stream s Identity TokenPos) => Parsec s u [TokenPos]
satisfyTypeIde = do
  first <- satisfyIde
  satisfyTypeIde' [first]

satisfyTypeIde' :: (Stream s Identity TokenPos) => [TokenPos] -> Parsec s u [TokenPos]
satisfyTypeIde' first = do
  maybeDot <- optionMaybe (satisfy Dot)
  case maybeDot of
    Just dotpos -> do
      next <- satisfyIde
      satisfyTypeIde' (next:((Dot,dotpos):first))
    Nothing -> return (reverse first)
