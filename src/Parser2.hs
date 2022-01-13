{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Parser2
  ( parseClasses2
  , Abstraction(..)
  , Value(..)
  , Term(..)
  , Extends(..)
  , ConstructorInvocation(..)
  , Assignment(..)
  , Signature(..)
  , Parameter(..)
  , Field(..)
  , Method(..)
  , MethodImplementation(..)
  , Clazz2(..)
  , SourcePos'(..)
  , TypeName(..)
  , TypeError(..) -- defined here to be shared by TypeInfo and TypeChecker
  , getClazz2Name
  , LocalClasses
  , isValidClass
  , getTermPosition
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
import ClassPath (ClassPath,hasClass)
import Lexer
    ( TokenPos,
      Token(Dot, LParens, Comma, Semi, RParens, Assign, Ide, Keyword, IntegerLiteral, StringLiteral, BooleanLiteral, Question, Colon) )
import Debug.Trace
import Control.Monad.Extra (ifM)
import Parser (NameToPackageMap)
import qualified Text.Read.Lex as L
import Text.ParserCombinators.ReadPrec

data Abstraction = FieldAccess SourcePos P.SimpleName
                 | MethodInvocation SourcePos P.SimpleName [Term]
                 deriving Show

data TypeName = TypeName SourcePos P.QualifiedName deriving Show

data Value = Variable SourcePos P.SimpleName
           | IntegerLit SourcePos Int32
           | StringLit SourcePos String
           | BooleanLit SourcePos Bool
           | ObjectCreation SourcePos TypeName [Term]
           deriving Show

data Term = Value Value
          | Application Term Abstraction
          | StaticApplication TypeName Abstraction
          | Conditional Term Term Term
          | Cast TypeName Term
          deriving Show

type ClassData = (ClassPath,LocalClasses)

data TypeError = TypeError String SourcePos'

instance Show TypeError where
  show (TypeError str pos) = str ++ "\nat: " ++ show pos

getTermPosition :: Term -> SourcePos
getTermPosition (Value (Variable pos _)) = pos
getTermPosition (Value (IntegerLit pos _)) = pos
getTermPosition (Value (StringLit pos _)) = pos
getTermPosition (Value (BooleanLit pos _)) = pos
getTermPosition (Value (ObjectCreation pos _ _)) = pos
getTermPosition (Cast (TypeName pos _) _) = pos
getTermPosition (Application t _) = getTermPosition t
getTermPosition (StaticApplication (TypeName pos _) _) = pos
getTermPosition (Conditional t _ _) = getTermPosition t

type LocalClasses = Map.Map P.QualifiedName Clazz2

data SourcePos' = SourcePos' SourcePos | CompiledCode

data Extends = NewExtends SourcePos P.QualifiedName | ExtendsObject

data ConstructorInvocation = NewConstructorInvocation SourcePos [Term] deriving Show

data Assignment = NewAssignment SourcePos Term SourcePos Term deriving Show

data Signature = Signature P.SimpleName [(P.QualifiedName,SourcePos)]

data Parameter = NewParameter SourcePos P.QualifiedName P.SimpleName deriving Show

data Field = NewField SourcePos P.QualifiedName  SourcePos P.SimpleName

data Method = NewMethod SourcePos P.SimpleName [Parameter] P.QualifiedName Signature MethodImplementation

data Clazz2 = NewClazz2 SourcePos P.CompilationUnit P.QualifiedName Extends [Field] [Method]

data MethodImplementation = MethodImpl Term | ConstructorImpl (Maybe ConstructorInvocation) [Assignment]

instance Show SourcePos' where
  show (SourcePos' pos) = show pos
  show CompiledCode = "Compiled Code"

{-- Parameters are equal if their types are equal. This is convenient in some cases, but might cause problems in others -}
instance Eq Parameter where
  (==) (NewParameter _ tp1 _) (NewParameter _ tp2 _) = tp1 == tp2

instance Show Signature where
  show (Signature nm types) = P.simpleNameToString nm ++ "(" ++ concatMap show types ++ ")"

instance TextShow Signature where
  showb s = fromString (show s)

instance Eq Signature where
  (==) (Signature nm1 types1) (Signature nm2 types2) = nm1 == nm2 && types1 == types2

instance Show Field where
  show (NewField _ tp _ nm) = show tp ++ " " ++ show nm ++ ";"

instance Show Method where
  show (NewMethod _ _ _ _ sig (MethodImpl term)) = show sig++"\n"++show term
  show (NewMethod _ _ _ _ sig (ConstructorImpl _ assignments)) = show sig++"\n"++foldr (\a str -> str++"\n"++show a) "" assignments

instance Show Extends where
  show (NewExtends _ qName) = "extends " ++ show qName
  show ExtendsObject = "extends /java/lang/Object"

instance Show Clazz2 where
  show (NewClazz2 _ _ nm extends fields methods) =
    "class " ++ show nm ++ " " ++ show extends ++ "\n" ++
      foldr (\f str -> show f++"\n"++str) "" fields ++
      foldr (\c str -> show c++"\n"++str) "" methods

getClazz2Name :: Clazz2 -> P.QualifiedName
getClazz2Name (NewClazz2 _ _ nm _ _ _) = nm

parseClasses2 :: [P.Clazz] -> Either ParseError (Map.Map P.QualifiedName Clazz2)
parseClasses2 clazzList = do
  let pairsList = fmap (\cls@(P.NewClazz _ _ nm _ _ _ _) -> (nm, cls)) clazzList
  let clazzMap = Map.fromList pairsList
  mapM (mapClazz clazzMap) clazzMap


mapClazz :: Map.Map P.QualifiedName P.Clazz -> P.Clazz -> Either ParseError Clazz2
mapClazz classMap (P.NewClazz pos cu name maybeExtends fields constructors methods) = do
  e <- case maybeExtends of Just tok -> mapExtends cu classMap tok; Nothing -> Right ExtendsObject;
  c <- mapM (mapConstructor cu classMap) constructors
  f <- mapM (mapField cu classMap) fields
  m <- mapM (mapMethod cu classMap) methods
  return (NewClazz2 pos cu name e f (c++m))

mapExtends :: P.CompilationUnit -> Map.Map P.QualifiedName P.Clazz -> [TokenPos] -> Either ParseError Extends
mapExtends P.CompilationUnit {..} classMap =
  runParser parseExtends (TermState {termStack=[],maybeTypeName=Nothing,..}) ""

mapField :: P.CompilationUnit -> Map.Map P.QualifiedName P.Clazz -> P.Field -> Either ParseError Field
mapField P.CompilationUnit {..} classMap (P.NewField toks) = do
  (tppos,tp,nmpos,nm) <- runParser parseField (TermState {termStack=[],maybeTypeName=Nothing,..}) "" toks
  return (NewField tppos tp nmpos nm)

mapConstructor :: P.CompilationUnit -> Map.Map P.QualifiedName P.Clazz -> P.Constructor -> Either ParseError Method
mapConstructor P.CompilationUnit {..} classMap (P.NewConstructor pos toks (P.NewBody bodyToks)) = do
  params <- runParser parameter (TermState  {termStack=[],maybeTypeName=Nothing,..}) "" toks
  (super, assignments) <- runParser constructorBody (TermState  {termStack=[],maybeTypeName=Nothing,..}) "" bodyToks
  return (NewMethod pos P.createNameInit params P.createQNameObject (createSignature P.createNameInit params) (ConstructorImpl super assignments))

mapMethod :: P.CompilationUnit -> Map.Map P.QualifiedName P.Clazz -> P.Method -> Either ParseError Method
mapMethod P.CompilationUnit {..} classMap (P.NewMethod tpTok nmTok paramsToks (P.NewBody bodyToks)) = do
  toks <- runParser satisfyQualifiedName (TermState {termStack=[],maybeTypeName=Nothing,..}) "" tpTok
  let (tp,_) = P.createQName package classMap imports toks
  let (nm,pos) = P.createName nmTok
  params <- runParser parameter (TermState {termStack=[],maybeTypeName=Nothing,..}) "" paramsToks
  body <- runParser methodBody (TermState {termStack=[],maybeTypeName=Nothing,..}) "" bodyToks
  return (NewMethod pos nm params tp (createSignature nm params) (MethodImpl body))

parseExtends :: (Stream s Identity TokenPos) => Parsec s TermState Extends
parseExtends = do
  TermState {..} <- getState
  toks <- satisfyQualifiedName
  let (qName,pos) = P.createQName package classMap imports toks
  return (if show qName == "/java/lang/Object" then ExtendsObject else NewExtends pos qName)

parseField :: (Stream s Identity TokenPos) => Parsec s TermState (SourcePos, P.QualifiedName, SourcePos, P.SimpleName)
parseField = do
  TermState {..} <- getState
  toks <- satisfyQualifiedName
  let (tp, tppos) = P.createQName package classMap imports toks
  tok <- P.satisfySimpleName
  let (nm,nmpos) = P.createName tok
  return (tppos,tp,nmpos,nm)

createSignature :: P.SimpleName -> [Parameter] -> Signature
createSignature nm params = Signature nm (fmap (\(NewParameter pos tp _) -> (tp,pos)) params)

constructorBody :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState (Maybe ConstructorInvocation, [Assignment])
constructorBody = do
  maybeSuper <- optionMaybe (try constructorInvocation)
  assignments <- assignmentList
  return (maybeSuper, assignments)

constructorInvocation :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState ConstructorInvocation
constructorInvocation = do
  pos <- satisfyKeyword "super"
  P.satisfy LParens
  arguments <- argumentList
  P.satisfy RParens
  P.satisfy Semi
  return (NewConstructorInvocation pos arguments)

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
      toks <- satisfyQualifiedName
      let (tp,tppos) = P.createQName package classMap imports toks
      tok <- P.satisfySimpleName
      let (name,nmpos) = P.createName tok
      fmap ([NewParameter tppos tp name] ++) nextParameter

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

data TermState = TermState {termStack :: [Term], maybeTypeName :: Maybe TypeName, package :: [T.Text], classMap :: Map.Map P.QualifiedName P.Clazz, imports :: P.NameToPackageMap, classpath :: ClassPath }

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
      case maybeTN of
        Just tn -> do
          (terminator, _) <- lookAhead anyToken
          case terminator of
              Dot -> do
                P.satisfy Dot
                putState (TermState {maybeTypeName=Just tn,..})
                try fieldAccessTerm <|> methodInvocationTerm
              _ -> parserFail ""
        Nothing -> do
          t <- try integerLiteralTerm <|>
              try stringLiteralTerm <|>
              try booleanLiteralTerm <|>
              try objectCreationTerm <|>
              try variableTerm <|>
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
  tpName <- typeName
  P.satisfy LParens
  arguments <- argumentList
  P.satisfy RParens
  return (Value (ObjectCreation pos tpName arguments))

variableThis :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
variableThis = do
  pos <- try $ satisfyKeyword "this"
  lookAhead expressionTerminator
  return (Value (Variable pos P.createNameThis))

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
    Just typeName@(TypeName pos tp) -> do
      putState (TermState {maybeTypeName=Nothing,..})
      return (StaticApplication typeName (FieldAccess pos name))
    Nothing -> case termStack of
      [] -> parserFail "Invalid field access application"
      (t:ts) -> do
        putState (TermState {termStack=ts,..})
        return (Application t (FieldAccess pos name))

methodInvocationTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
methodInvocationTerm = do
  TermState {..} <- getState
  tok <- P.satisfySimpleName
  let (method,pos) = P.createName tok
  P.satisfy LParens
  putState (TermState {termStack=[],maybeTypeName=Nothing,..})
  arguments <- argumentList
  putState (TermState {..})
  P.satisfy RParens
  case maybeTypeName of
    Just typeName@(TypeName pos tp) -> do
      putState (TermState {maybeTypeName=Nothing,..})
      return (StaticApplication typeName (MethodInvocation pos method arguments))
    Nothing -> case termStack of
      [] -> parserFail "Invalid method invocation application"
      (t:ts) -> do
        putState (TermState {termStack=ts,..})
        return (Application t (MethodInvocation pos method arguments))

castTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
castTerm = do
  TermState {..} <- getState
  pos <- P.satisfy LParens
  tpName <- typeName
  P.satisfy RParens
  Cast tpName <$> term

expressionTerminator :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState SourcePos
expressionTerminator =  P.satisfy Dot
                    <|> P.satisfy Comma
                    <|> P.satisfy Semi
                    <|> P.satisfy RParens
                    <|> P.satisfy Assign
                    <|> P.satisfy Question
                    <|> P.satisfy Colon

typeName :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState TypeName
typeName = do
  TermState {..} <- getState
  tok <- P.satisfySimpleName
  let sn = P.deconstructSimpleName $ fst $ P.createName tok
  let (qn,pos) = P.createQName package classMap imports [tok]
  if isValidClass classMap classpath qn
    then do
      lookAhead (try expressionTerminator <|> P.satisfy LParens)
      return $ TypeName pos qn
    else typeName' [tok] pos

typeName' :: (Stream s Identity (Token, SourcePos)) => [TokenPos] -> SourcePos -> Parsec s TermState TypeName
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
          lookAhead (try expressionTerminator <|> P.satisfy LParens)
          return $ TypeName pos qn
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
                        (snd)
                        (\(tok, pos) -> case tok of BooleanLiteral b -> Just (b, pos); _ -> Nothing)

satisfyQualifiedName :: (Stream s Identity TokenPos) => Parsec s u [TokenPos]
satisfyQualifiedName = do
 first <- P.satisfySimpleName
 satisfyQualifiedName' [first]

satisfyQualifiedName' :: (Stream s Identity TokenPos) => [TokenPos] -> Parsec s u [TokenPos]
satisfyQualifiedName' first = do
 maybeDot <- optionMaybe (P.satisfy Dot)
 case maybeDot of
   Just dotpos -> do
     next <- P.satisfySimpleName
     satisfyQualifiedName' (next:first)
   Nothing -> return first

{--Does the given QualifiedName exist as a class being compiled, or a class in the classpash -}
isValidClass :: Map.Map P.QualifiedName P.Clazz -> ClassPath -> P.QualifiedName -> Bool
isValidClass classMap cp tp =
  Map.member tp classMap || hasClass cp (toText (showb tp))
