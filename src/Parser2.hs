{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StrictData #-}

{-- Parse the components of a Parser.Clazz -}
module Parser2
  ( parseClasses2
  , Abstraction(..)
  , Value(..)
  , Term(..)
  , ClassReference(..)
  , ConstructorInvocation(..)
  , SuperConstructorInvocation(..)
  , ApplicationTarget(..)
  , Assignment(..)
  , Signature(..)
  , Parameter(..)
  , Field(..)
  , Method(..)
  , MethodImplementation(..)
  , Clazz2(..)
  , TypeArgument(..)
  , WildcardBounds(..)
  , PrimitiveType(..)
  , ReferenceType(..)
  , JavaType(..)
  , TypeError(..) -- defined here to be shared by TypeInfo and TypeChecker
  , LocalClasses
  , getTermPosition
  , MethodAccessFlag
  , ClassAccessFlag
  ) where

import TextShow
import Data.Functor.Identity (Identity)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Data.Maybe(isNothing)
import Data.List (intercalate,foldl')
import Data.Int (Int32)
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.Parsec.Pos
import Text.Parsec.Error
import qualified Parser as P
import ClassPath (ClassPath,hasClass,createValidTypeRefTypeObject)
import Lexer
    ( TokenPos,
      Token(Dot, LParens, Comma, Semi, RParens, Assign, Ide, Keyword, IntegerLiteral, StringLiteral, BooleanLiteral, Question, Colon, LAngleBracket, RAngleBracket, IntegralTypeTok, BooleanTypeTok) )
import Debug.Trace
import Control.Monad.Extra (ifM)
import Parser (NameToPackageMap)
import qualified Text.Read.Lex as L
import Text.ParserCombinators.ReadPrec
import TypeCheckerTypes

data Abstraction = FieldAccess SourcePos P.SimpleName
                 | MethodInvocation SourcePos P.SimpleName [Term] [TypeArgument]
                 | SuperMethodInvocation SourcePos P.SimpleName [Term]
                 deriving Show

data Value = Variable SourcePos P.SimpleName
           | IntegerLit SourcePos Int32
           | StringLit SourcePos String
           | BooleanLit SourcePos Bool
           | ObjectCreation SourcePos ReferenceType [Term] [TypeArgument]
           deriving Show

data ApplicationTarget = ApplicationTargetTerm Term
                       | ApplicationTargetTypeName ReferenceType
                       deriving Show

data Term = Value Value
          | Application ApplicationTarget Abstraction
          | Conditional Term Term Term
          | Cast ReferenceType Term
          deriving Show

type ClassData = (ClassPath,LocalClasses)

data TypeError = TypeError String SourcePos

data TypeArgument = ReferenceTypeArgument ReferenceType
                  | WildcardArgument WildcardBounds
                  deriving Show

data WildcardBounds = ExtendsBounds ReferenceType
                    | SuperBounds ReferenceType
                    deriving Show

data PrimitiveType = PrimitiveIntegralType SourcePos | PrimitiveBooleanType SourcePos deriving Show

data ReferenceType = ClassType SourcePos P.QualifiedName [TypeArgument]
                   | TypeVariable SourcePos P.SimpleName
                   deriving Show

data JavaType = JavaPrimitiveType PrimitiveType | JavaReferenceType ReferenceType deriving Show

instance Show TypeError where
  show (TypeError str pos) = str ++ "\nat: " ++ show pos

getTermPosition :: Term -> SourcePos
getTermPosition (Value (Variable pos _)) = pos
getTermPosition (Value (IntegerLit pos _)) = pos
getTermPosition (Value (StringLit pos _)) = pos
getTermPosition (Value (BooleanLit pos _)) = pos
getTermPosition (Value (ObjectCreation pos _ _ _)) = pos
getTermPosition (Cast (ClassType pos _ _) _) = pos
getTermPosition (Cast (TypeVariable pos _) _) = pos
getTermPosition (Application (ApplicationTargetTerm t) _) = getTermPosition t
getTermPosition (Application (ApplicationTargetTypeName (ClassType pos _ _)) _) = pos
getTermPosition (Application (ApplicationTargetTypeName (TypeVariable pos _)) _) = pos
getTermPosition (Conditional t _ _) = getTermPosition t

type LocalClasses = Map.Map P.QualifiedName Clazz2

data ClassReference = ClassReference SourcePos P.QualifiedName [TypeArgument]

data ConstructorInvocation = NewConstructorInvocation SourcePos [Term] deriving Show

data SuperConstructorInvocation = NewSuperConstructorInvocation SourcePos [Term] deriving Show

data Assignment = NewAssignment SourcePos Term SourcePos Term deriving Show

data Signature = Signature P.SimpleName [JavaType]

data Parameter = NewParameter JavaType SourcePos P.SimpleName deriving Show

data Field = NewField JavaType SourcePos P.SimpleName

data Method = NewMethod SourcePos [P.MethodAccessFlag] P.SimpleName [Parameter] JavaType Signature (Maybe MethodImplementation)

data Clazz2 = NewClazz2 SourcePos P.CompilationUnit [P.ClassAccessFlag] P.QualifiedName (Maybe ClassReference) [ClassReference] [Field] [Method]

data MethodImplementation = MethodImpl Term | ConstructorImpl (Either ConstructorInvocation SuperConstructorInvocation) [Assignment]

instance Show Signature where
  show (Signature nm types) = P.simpleNameToString nm ++ "(" ++ concatMap show types ++ ")"

instance TextShow Signature where
  showb s = fromString (show s)

instance Show Field where
  show (NewField tp _ nm) = show tp ++ " " ++ show nm ++ ";"

instance Show Method where
  show (NewMethod _ _ _ _ _ sig (Just (MethodImpl term))) = show sig++"\n"++show term
  show (NewMethod _ _ _ _ _ sig (Just (ConstructorImpl _ assignments))) = show sig++"\n"++foldr (\a str -> str++"\n"++show a) "" assignments
  show (NewMethod _ _ _ _ _ sig Nothing) = show sig

instance Show ClassReference where
  show (ClassReference _ qName typeArgs) = show qName ++
    if null typeArgs then "" else "<"++intercalate ", " (fmap show typeArgs)++">"

instance Show Clazz2 where
  show (NewClazz2 _ _ af nm extends implements fields methods) =
    abs++"class "++show nm++" extends "++show extends++(if null implements then "" else " implements "++intercalate "," (fmap show implements))++"\n"++
      foldr (\f str -> show f++"\n"++str) "" fields ++
      foldr (\c str -> show c++"\n"++str) "" methods
    where
      abs = if P.CAbstract `elem` af then "abstract " else ""

parseClasses2 :: [P.Clazz] -> Either ParseError (Map.Map P.QualifiedName Clazz2)
parseClasses2 clazzList = do
  let pairsList = fmap (\cls@P.NewClazz{clazzName=nm} -> (nm, cls)) clazzList
  let clazzMap = Map.fromList pairsList
  mapM (mapClazz clazzMap) clazzMap


mapClazz :: Map.Map P.QualifiedName P.Clazz -> P.Clazz -> Either ParseError Clazz2
mapClazz classMap P.NewClazz{..} = do
  e <- case maybeSuperClazzName of Just superClazzToks -> Just <$> mapExtends complilationUnit classMap superClazzToks; Nothing -> Right Nothing;
  i <- mapImplements complilationUnit classMap interfaceClazzNames
  f <- mapM (mapField complilationUnit classMap) fields
  c <- mapM (mapConstructor complilationUnit classMap) constructors
  m <- mapM (mapMethod complilationUnit classMap) methods
  return (NewClazz2 pos complilationUnit accessFlags clazzName e i f (c++m))

mapExtends :: P.CompilationUnit -> Map.Map P.QualifiedName P.Clazz -> [TokenPos] -> Either ParseError ClassReference
mapExtends P.CompilationUnit {..} classMap =
  runParser parseClassReference (TermState {termStack=[],maybeTypeName=Nothing,..}) ""

mapImplements :: P.CompilationUnit -> Map.Map P.QualifiedName P.Clazz -> [TokenPos] -> Either ParseError [ClassReference]
mapImplements P.CompilationUnit {..} classMap =
  runParser (sepBy parseClassReference (P.satisfy Comma)) (TermState {termStack=[],maybeTypeName=Nothing,..}) ""

mapField :: P.CompilationUnit -> Map.Map P.QualifiedName P.Clazz -> P.Field -> Either ParseError Field
mapField P.CompilationUnit {..} classMap (P.NewField typeToks nmTok) = do
  fieldType <- runParser parseJavaType  (TermState {termStack=[],maybeTypeName=Nothing,..}) "" typeToks
  let (nm,nmpos) = P.createName nmTok
  trace ("field: "++show nm++" = "++show fieldType) return (NewField fieldType nmpos nm)

mapConstructor :: P.CompilationUnit -> Map.Map P.QualifiedName P.Clazz -> P.Constructor -> Either ParseError Method
mapConstructor P.CompilationUnit {..} classMap (P.NewConstructor pos toks (P.NewBody bodyToks)) = do
  params <- runParser parameter (TermState  {termStack=[],maybeTypeName=Nothing,..}) "" toks
  (constructorInv, assignments) <- runParser constructorBody (TermState  {termStack=[],maybeTypeName=Nothing,..}) "" bodyToks
  return (NewMethod pos
                    []
                    P.createNameInit
                    params
                    (JavaReferenceType (ClassType pos P.createQNameObject []))
                    (createSignature P.createNameInit params)
                    (Just (ConstructorImpl constructorInv assignments)))
mapConstructor P.CompilationUnit {..} classMap (P.NewConstructor pos toks P.EmptyBody) =
  undefined

mapMethod :: P.CompilationUnit -> Map.Map P.QualifiedName P.Clazz -> P.Method -> Either ParseError Method
mapMethod P.CompilationUnit {..} classMap (P.NewMethod accessFlags tpTok nmTok paramsToks body) = do
  tp <- runParser parseJavaType  (TermState {termStack=[],maybeTypeName=Nothing,..}) "" tpTok
  let (nm,pos) = P.createName nmTok
  params <- runParser parameter (TermState {termStack=[],maybeTypeName=Nothing,..}) "" paramsToks
  case body of
    (P.NewBody bodyToks) -> do
      parsedBody <- runParser methodBody (TermState {termStack=[],maybeTypeName=Nothing,..}) "" bodyToks
      return (NewMethod pos accessFlags nm params tp (createSignature nm params) (Just (MethodImpl parsedBody)))
    P.EmptyBody ->
      return (NewMethod pos accessFlags nm params tp (createSignature nm params) Nothing)

parseClassReference :: (Stream s Identity TokenPos) => Parsec s TermState ClassReference
parseClassReference = do
  TermState {..} <- getState
  toks <- satisfyQualifiedName
  typeArgs <- parseTypeArguments
  let (qName,pos) = P.createQName package classMap imports toks
  return $ ClassReference pos qName typeArgs

parseTypeArguments :: (Stream s Identity TokenPos) => Parsec s TermState [TypeArgument]
parseTypeArguments = do
  maybeTypeArgsStart <- optionMaybe (P.satisfy LAngleBracket)
  case maybeTypeArgsStart of
    Nothing -> return []
    Just _ -> do
      typeArgs <- parseTypeArguments'
      P.satisfy RAngleBracket
      return $ typeArgs

parseJavaType :: (Stream s Identity TokenPos) => Parsec s TermState JavaType
parseJavaType = do
  maybePrimitiveType <- optionMaybe parsePrimitiveType
  case maybePrimitiveType of
    Just pt -> return (JavaPrimitiveType pt)
    Nothing -> JavaReferenceType <$> parseReferenceType

parsePrimitiveType :: (Stream s Identity TokenPos) => Parsec s TermState PrimitiveType
parsePrimitiveType = do
  maybePrimitiveType <- try (P.satisfy IntegralTypeTok) <|> (P.satisfy BooleanTypeTok)
  return $ case maybePrimitiveType of
    (IntegralTypeTok,pos) -> PrimitiveIntegralType pos
    (BooleanTypeTok,pos) -> PrimitiveBooleanType pos
    _ -> undefined

parseReferenceType :: (Stream s Identity TokenPos) => Parsec s TermState ReferenceType
parseReferenceType = do
  TermState {..} <- getState
  qnToks <- satisfyQualifiedName
  typeArgs <- parseTypeArguments
  let (qn,pos) = P.createQName package classMap imports qnToks
  return $ ClassType pos qn typeArgs

parseReferenceTypes :: (Stream s Identity TokenPos) => Parsec s TermState [ReferenceType]
parseReferenceTypes = do
  refType <- parseReferenceType
  maybeComma <- optionMaybe (P.satisfy Comma)
  case maybeComma of
    Nothing -> return [refType]
    Just _ -> do
      (refType :) <$> parseReferenceTypes

data Direction = Extends | Super

parseTypeArgument :: (Stream s Identity TokenPos) => Parsec s TermState TypeArgument
parseTypeArgument = do
  TermState {..} <- getState
  maybeQuestionTok <- optionMaybe $ try (P.satisfy Question)
  case maybeQuestionTok of
    Just (_,questionMarkPos) -> do
      maybeWildcardBounds <- optionMaybe $
        try
          ((satisfyKeyword "extends" >> (,) Extends <$> parseReferenceType) <|>
           (satisfyKeyword "super" >> (,) Super <$> parseReferenceType))
      return $ case maybeWildcardBounds of
        Nothing -> WildcardArgument (ExtendsBounds (ClassType questionMarkPos createQNameObject []))
        Just (direction, rtw) -> case direction of
          Extends -> WildcardArgument (ExtendsBounds rtw)
          Super -> WildcardArgument (SuperBounds rtw)
    Nothing -> do
      qnToks <- satisfyQualifiedName
      typeArgs <- parseTypeArguments
      let (qn,pos) = P.createQName package classMap imports qnToks
      return $ ReferenceTypeArgument (ClassType pos qn typeArgs)

parseTypeArguments' :: (Stream s Identity TokenPos) => Parsec s TermState [TypeArgument]
parseTypeArguments' = do
  refType <- parseTypeArgument
  maybeComma <- optionMaybe (P.satisfy Comma)
  case maybeComma of
    Nothing -> return [refType]
    Just _ -> do
      (refType :) <$> parseTypeArguments'

createSignature :: P.SimpleName -> [Parameter] -> Signature
createSignature nm params = Signature nm (fmap (\(NewParameter tp _ _) -> tp) params)

constructorBody :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState (Either ConstructorInvocation SuperConstructorInvocation, [Assignment])
constructorBody = do
  maybeSuper <- optionMaybe (try superConstructorInvocation)
  maybeThis <- optionMaybe (try constructorInvocation)
  assignments <- assignmentList
  case maybeSuper of
    Nothing -> case maybeThis of
      Nothing -> parserFail "invocation of this or super required in constructor"
      Just ci -> return (Left ci, assignments)
    Just sci -> case maybeThis of
      Nothing -> return (Right sci, assignments)
      Just ci -> parserFail "this and super not allowed in same constructor"

constructorInvocation :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState ConstructorInvocation
constructorInvocation = do
  pos <- satisfyKeyword "this"
  P.satisfy LParens
  arguments <- argumentList
  P.satisfy RParens
  P.satisfy Semi
  return (NewConstructorInvocation pos arguments)

superConstructorInvocation :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState SuperConstructorInvocation
superConstructorInvocation = do
  pos <- satisfyKeyword "super"
  P.satisfy LParens
  arguments <- argumentList
  P.satisfy RParens
  P.satisfy Semi
  return (NewSuperConstructorInvocation pos arguments)

methodBody :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
methodBody = do
  satisfyKeyword "return"
  t <-term
  TermState {..} <- getState
  if not (null termStack)
  then fail $ "Expression application leaves unconsumed terms: "++foldl' (\str tm -> show tm++str) "" termStack
  else do
    P.satisfy Semi
    return t

termList' :: (Stream s Identity (Token, SourcePos)) => Token -> Parsec s TermState [Term]
termList' delimitter = do
  t <- term
  maybeDelimitter <- optionMaybe (P.satisfy delimitter)
  case maybeDelimitter of
    Just _ ->
      fmap ([t] ++) (termList' delimitter)
    Nothing -> return [t]

argumentList :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState [Term]
argumentList = do
  maybeEmpty <- optionMaybe (lookAhead (P.satisfy RParens))
  case maybeEmpty of
    Just _ -> return []
    Nothing -> termList' Comma

parameter :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState [Parameter]
parameter = do
  maybeEof <- optionMaybe eof
  case maybeEof of
    Just _ -> return []
    Nothing -> do
      TermState {..} <- getState
      tp <- parseJavaType
      tok <- P.satisfySimpleName
      let (name,nmpos) = P.createName tok
      fmap ([NewParameter tp nmpos name] ++) nextParameter

nextParameter :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState [Parameter]
nextParameter = do
  optional (P.satisfy Comma)
  parameter

assignmentList :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState [Assignment]
assignmentList = do
  maybeAssignment <- optionMaybe assignment
  case maybeAssignment of
    Just a -> do
      P.satisfy Semi
      fmap ([a] ++) assignmentList
    Nothing -> return []

assignment :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Assignment
assignment = do
  variable <- term
  P.satisfy Assign
  t <- term
  return $ NewAssignment (getTermPosition variable) variable (getTermPosition t) t

data TermState = TermState {termStack :: [Term], maybeTypeName :: Maybe ReferenceType, package :: [T.Text], classMap :: Map.Map P.QualifiedName P.Clazz, imports :: P.NameToPackageMap, classpath :: ClassPath }

term :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
term = do
  TermState {..} <- getState
  maybeParens <- optionMaybe $ P.satisfy LParens
  case maybeParens of
    Just pos -> do
      maybeTN <- optionMaybe $ try typeName
      case maybeTN of
        Just tn -> do
          maybeRParens <- optionMaybe $ P.satisfy RParens
          case maybeRParens of
            Just _ -> Cast tn <$> term
            Nothing ->
              case maybeTypeName of
                Just _ -> parserFail "Invalid double typeName"
                Nothing -> do
                  putState (TermState {maybeTypeName=Just tn,termStack=[],..})
                  t <- term
                  putState (TermState {maybeTypeName=Nothing,..})
                  return t
        Nothing -> do
          case maybeTypeName of
            Just _ -> fail "Unconsumed type name"
            Nothing -> do
              putState (TermState {termStack=[],..})
              t <- term
              P.satisfy RParens
              putState (TermState {..})
              (terminator, _) <- lookAhead anyToken
              case terminator of
                  Dot -> do
                    TermState {..} <- getState
                    P.satisfy Dot
                    putState (TermState {termStack=t:termStack,..})
                    term
                  _ -> return t
    Nothing -> do
      maybeTN <- optionMaybe $ try typeName
      t <- case maybeTN of
        Just tn -> do
          (terminator, _) <- lookAhead anyToken
          case terminator of
              Dot -> do
                P.satisfy Dot
                putState (TermState {maybeTypeName=Just tn,..})
                try fieldAccessTerm <|> methodInvocationTerm
              _ -> parserFail ""
        Nothing -> do
          try integerLiteralTerm <|>
            try stringLiteralTerm <|>
            try booleanLiteralTerm <|>
            try objectCreationTerm <|>
            try variableTerm <|>
            try variableSuper <|>
            try variableThis <|>
            try fieldAccessTerm <|>
            try methodInvocationTerm
      (terminator, _) <- lookAhead anyToken
      case terminator of
          Dot -> do
            TermState {..} <- getState
            P.satisfy Dot
            putState (TermState {termStack=t:termStack,..})
            term
          Question -> do
            TermState {..} <- getState
            P.satisfy Question
            v1 <- term
            P.satisfy Colon
            Conditional t v1 <$> term
          _ -> return t

integerLiteralTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
integerLiteralTerm = do
  (value,pos) <- satisfyIntegerLiteral
  return (Value (IntegerLit pos value))

stringLiteralTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
stringLiteralTerm = do
  (value,pos) <- satisfyStringLiteral
  return (Value (StringLit pos value))

booleanLiteralTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
booleanLiteralTerm = do
  (value,pos) <- satisfyBooleanLiteral
  return (Value (BooleanLit pos value))

objectCreationTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
objectCreationTerm = do
  TermState {..} <- getState
  pos <- getPosition
  satisfyKeyword "new"
  constructorTypeArgs <- parseTypeArguments
  tpName <- parseReferenceType
  P.satisfy LParens
  arguments <- argumentList
  P.satisfy RParens
  return (Value (ObjectCreation pos tpName arguments constructorTypeArgs))

variableThis :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
variableThis = do
  pos <- try $ satisfyKeyword "this"
  lookAhead expressionTerminator
  return (Value (Variable pos P.createNameThis))

variableSuper :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
variableSuper = do
  pos <- try $ satisfyKeyword "super"
  lookAhead expressionTerminator
  return (Value (Variable pos P.createNameSuper))

variableTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
variableTerm = do
  TermState {..} <- getState
  if null termStack && isNothing maybeTypeName
    then do
      tok <- P.satisfySimpleName
      let (name,pos) = P.createName tok
      lookAhead expressionTerminator
      return (Value (Variable pos name))
    else parserFail "No variable. Term stack is not empty or type name present."

fieldAccessTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
fieldAccessTerm = do
  TermState {..} <- getState
  tok <- P.satisfySimpleName
  let (name,pos) = P.createName tok
  lookAhead expressionTerminator
  case maybeTypeName of
    Just typeName@(ClassType pos _ _) -> do
      putState (TermState {maybeTypeName=Nothing,..})
      return (Application (ApplicationTargetTypeName typeName) (FieldAccess pos name))
    Just typeVariable@(TypeVariable _ _) -> undefined
    Nothing -> case termStack of
      [] -> parserFail "Invalid field access application"
      (t:ts) -> do
        putState (TermState {termStack=ts,..})
        return (Application (ApplicationTargetTerm t) (FieldAccess pos name))

methodInvocationTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
methodInvocationTerm = do
  TermState {..} <- getState
  typeArgs <- parseTypeArguments
  tok <- P.satisfySimpleName
  let (method,pos) = P.createName tok
  P.satisfy LParens
  putState (TermState {termStack=[],maybeTypeName=Nothing,..})
  arguments <- argumentList
  putState (TermState {..})
  P.satisfy RParens
  case maybeTypeName of
    Just typeName@(ClassType pos _ _) -> do
      putState (TermState {maybeTypeName=Nothing,..})
      return (Application (ApplicationTargetTypeName typeName) (MethodInvocation pos method arguments typeArgs))
    Just typeVariable@(TypeVariable _ _) -> undefined
    Nothing -> case termStack of
      [] -> parserFail "Invalid method invocation application"
      (t:ts) -> do
        putState (TermState {termStack=ts,..})
        case t of
          Value (Variable pos' nm) | nm == P.createNameSuper ->
            return
              (Application
                (ApplicationTargetTerm
                  (Value (Variable pos' P.createNameThis)))
                (SuperMethodInvocation pos method arguments))
          _ ->
            return
              (Application
                (ApplicationTargetTerm t)
                (MethodInvocation pos method arguments typeArgs))

castTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
castTerm = do
  TermState {..} <- getState
  pos <- P.satisfy LParens
  tpName <- typeName
  P.satisfy RParens
  Cast tpName <$> term

expressionTerminator :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState TokenPos
expressionTerminator =  P.satisfy Dot
                    <|> P.satisfy Comma
                    <|> P.satisfy Semi
                    <|> P.satisfy RParens
                    <|> P.satisfy RAngleBracket
                    <|> P.satisfy Assign
                    <|> P.satisfy Question
                    <|> P.satisfy Colon

typeName :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState ReferenceType
typeName = do
  TermState {..} <- getState
  tok <- P.satisfySimpleName
  let sn = P.deconstructSimpleName $ fst $ P.createName tok
  let (qn,pos) = P.createQName package classMap imports [tok]
  if isValidClass classMap classpath qn
    then do
      typeArgs <- parseTypeArguments
      lookAhead (try expressionTerminator <|> P.satisfy LParens)
      return $ ClassType pos qn typeArgs
    else typeName' [tok] pos

typeName' :: (Stream s Identity (Token, SourcePos)) => [TokenPos] -> SourcePos -> Parsec s TermState ReferenceType
typeName' first pos = do
  TermState {..} <- getState
  maybeDot <- optionMaybe (P.satisfy Dot)
  case maybeDot of
    Just dotpos -> do
      next <- P.satisfySimpleName
      let sn = P.deconstructSimpleName $ fst $ P.createName next
      let (qn,_) = P.createQName [] classMap imports (next:first)
      if isValidClass classMap classpath qn
        then do
          typeArgs <- parseTypeArguments
          lookAhead (try expressionTerminator <|> P.satisfy LParens)
          return $ ClassType pos qn typeArgs
        else typeName' (next:first) pos
    Nothing -> fail "Not a valid type"

satisfyIde :: (Stream s Identity (Token, SourcePos)) => Parsec s u (T.Text, SourcePos)
satisfyIde = token (\(tok, pos) -> show tok)
                  (snd)
                  (\(tok, pos) -> case tok of Ide s -> Just (s,pos); _ -> Nothing)

satisfyKeyword :: (Stream s Identity (Token, SourcePos)) => String -> Parsec s u SourcePos
satisfyKeyword k = token (\(tok, pos) -> show tok)
                         (snd)
                         (\(tok, pos) -> case tok of Keyword n -> if n == k then Just pos else Nothing; _ -> Nothing)

satisfyIntegerLiteral :: (Stream s Identity (Token, SourcePos)) => Parsec s u (Int32, SourcePos)
satisfyIntegerLiteral = token (\(tok, pos) -> show tok)
                        (snd)
                        (\(tok, pos) -> case tok of IntegerLiteral n -> Just (n, pos); _ -> Nothing)

satisfyStringLiteral :: (Stream s Identity (Token, SourcePos)) => Parsec s u (String, SourcePos)
satisfyStringLiteral = token (\(tok, pos) -> show tok)
                        (snd)
                        (\(tok, pos) -> case tok of StringLiteral s -> Just (s, pos); _ -> Nothing)

satisfyBooleanLiteral :: (Stream s Identity (Token, SourcePos)) => Parsec s u (Bool, SourcePos)
satisfyBooleanLiteral = token (\(tok, pos) -> show tok)
                        snd
                        (\(tok, pos) -> case tok of BooleanLiteral b -> Just (b, pos); _ -> Nothing)

satisfyQualifiedName :: (Stream s Identity TokenPos) => Parsec s u [TokenPos]
satisfyQualifiedName = do
 first <- P.satisfySimpleName
 reverse <$> ((first :) <$> satisfyQualifiedName')

satisfyQualifiedName' :: (Stream s Identity TokenPos) => Parsec s u [TokenPos]
satisfyQualifiedName' = do
 maybeDot <- optionMaybe (P.satisfy Dot)
 case maybeDot of
   Just _ -> do
     next <- P.satisfySimpleName
     (next :) <$> satisfyQualifiedName'
   Nothing -> return []

{--Does the given QualifiedName exist as a class being compiled, or a class in the classpash -}
isValidClass :: Map.Map P.QualifiedName P.Clazz -> ClassPath -> P.QualifiedName -> Bool
isValidClass classMap cp tp =
  Map.member tp classMap || hasClass cp tp
