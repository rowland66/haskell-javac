{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Parser2
  ( parseClasses2
  , Abstraction(..)
  , Value(..)
  , Term(..)
  , DataType
  , Extends(..)
  , ConstructorInvocation(..)
  , Assignment(..)
  , Signature(..)
  , Parameter(..)
  , Field(..)
  , Constructor(..)
  , Method(..)
  , Clazz2(..)
  , SourcePos'(..)
  , getClazz2Name
  ) where

import Data.Functor.Identity (Identity)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Data.List (intersperse)
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.Parsec.Pos
import Text.Parsec.Error
import qualified Parser as P
import Lexer
import Debug.Trace

data Abstraction = FieldAccess SourcePos P.SimpleName
                 | MethodInvocation SourcePos P.SimpleName [Term]
                 deriving Show

data Value = Variable SourcePos P.SimpleName
          | ObjectCreation SourcePos P.QualifiedName [Term]
          | Cast SourcePos P.QualifiedName Term
          deriving Show

data Term = Value Value | Application Term Abstraction deriving Show

getTermPosition :: Term -> SourcePos
getTermPosition (Value (Variable pos _)) = pos
getTermPosition (Value (ObjectCreation pos _ _)) = pos
getTermPosition (Value (Cast pos _ _)) = pos
getTermPosition (Application t _) = getTermPosition t

type DataType = String;

data SourcePos' = SourcePos' SourcePos | CompiledCode

data Extends = NewExtends SourcePos P.QualifiedName | ExtendsObject

data ConstructorInvocation = NewConstructorInvocation SourcePos [Term] deriving Show

data Assignment = NewAssignment SourcePos Term Term deriving Show

data Signature = Signature P.SimpleName [P.QualifiedName]

data Parameter = NewParameter SourcePos P.QualifiedName P.SimpleName deriving Show

data Field = NewField SourcePos P.QualifiedName SourcePos P.SimpleName

data Constructor = NewConstructor SourcePos' [Parameter] Signature (Maybe ConstructorInvocation) [Assignment]

data Method = NewMethod SourcePos P.SimpleName [Parameter] P.QualifiedName Signature Term

data Clazz2 = NewClazz2 SourcePos' P.QualifiedName Extends [Field] [Constructor] [Method]

{-- Parameters are equal if their types are equal. This is convenient in some cases, but might cause problems in others -}
instance Eq Parameter where
  (==) (NewParameter _ tp1 _) (NewParameter _ tp2 _) = (tp1 == tp2)

instance Show Signature where
  show (Signature nm types) = (P.simpleNameToString nm) ++ "(" ++ (concat (intersperse "," (fmap show types))) ++ ")"

instance Eq Signature where
  (==) (Signature nm1 types1) (Signature nm2 types2) = (nm1 == nm2) && (types1 == types2)

instance Show Field where
  show (NewField _ tp _ nm) = (show tp) ++ " " ++ (show nm) ++ ";"

instance Show Constructor where
  show (NewConstructor _ _ sig _ assignments) = (show sig)++"\n"++(foldr (\a str -> str++"\n"++(show a)) "" assignments)

instance Show Method where
  show (NewMethod _ _ _ _ sig term) = (show sig)++"\n"++(show term)

instance Show Extends where
  show (NewExtends _ qName) = "extends " ++ (show qName)
  show (ExtendsObject) = "extends /java/lang/Object"

instance Show Clazz2 where
  show (NewClazz2 _ nm extends fields constructors methods) =
    "class " ++ (show nm) ++ " " ++ (show extends) ++ "\n" ++
      (foldr (\f str -> (show f)++"\n"++str) "" fields) ++
      foldr (\c str -> (show c)++"\n"++str) "" constructors

getClazz2Name :: Clazz2 -> P.QualifiedName
getClazz2Name (NewClazz2 _ nm _ _ _ _) = nm

parseClasses2 :: [P.Clazz] -> (Either ParseError (Map.Map P.QualifiedName Clazz2))
parseClasses2 clazzList = do
  clazzList <- sequence (fmap (\cls -> mapClazz cls) clazzList)
  let pairsList = fmap (\cls@(NewClazz2 _ nm _ _ _ _) -> (nm, cls)) clazzList
  trace "Parser2" $ return (Map.fromList pairsList)

mapClazz :: P.Clazz -> Either ParseError Clazz2
mapClazz (P.NewClazz pos package _ name maybeExtends fields constructors methods) = do
  e <- case maybeExtends of Just tok -> (mapExtends package tok); Nothing -> Right ExtendsObject;
  c <- sequence (fmap (mapConstructor package) constructors)
  f <- sequence (fmap (mapField package) fields)
  m <- sequence (fmap (mapMethod package) methods)
  return (NewClazz2 (SourcePos' pos) name e f c m)

mapExtends :: [T.Text] -> [TokenPos] -> Either ParseError Extends
mapExtends package toks = runParser parseExtends (TermState {package=package, termStack=[]}) "" toks

mapField :: [T.Text] -> P.Field -> Either ParseError Field
mapField package (P.NewField toks) = do
  (tppos,tp,nmpos,nm) <- runParser parseField (TermState {package=package,termStack=[]}) "" toks
  return (NewField tppos tp nmpos nm)

mapConstructor :: [T.Text] -> P.Constructor -> Either ParseError Constructor
mapConstructor package (P.NewConstructor pos toks (P.NewBody bodyToks)) = do
  params <- runParser parameter (TermState  {package=package, termStack=[]}) "" toks
  (super, assignments) <- runParser constructorBody (TermState  {package=package, termStack=[]}) "" bodyToks
  return (NewConstructor (SourcePos' pos) params (createSignature P.createNameInit params) super assignments)

mapMethod :: [T.Text] -> P.Method -> Either ParseError Method
mapMethod package (P.NewMethod tpTok nmTok paramsToks (P.NewBody bodyToks)) = do
  toks <- runParser satisfyQualifiedName (TermState {package=package, termStack=[]}) "" tpTok
  let (tp,_) = P.createQName package toks
  let (nm,pos) = P.createName nmTok
  params <- runParser parameter (TermState {package=package, termStack=[]}) "" paramsToks
  body <- runParser methodBody (TermState {package=package, termStack=[]}) "" bodyToks
  return (NewMethod pos nm params tp (createSignature nm params) body)

parseExtends :: (Stream s Identity TokenPos) => Parsec s TermState Extends
parseExtends = do
  TermState {..} <- getState
  toks <- satisfyQualifiedName
  let (qName,pos) = P.createQName package toks
  return (if ((show qName) == "/java/lang/Object") then ExtendsObject else (NewExtends pos qName))

parseField :: (Stream s Identity TokenPos) => Parsec s TermState (SourcePos, P.QualifiedName, SourcePos, P.SimpleName)
parseField = do
  TermState {..} <- getState
  toks <- satisfyQualifiedName
  let (tp, tppos) = P.createQName package toks
  tok <- P.satisfySimpleName
  let (nm,nmpos) = P.createName tok
  trace ("field type: "++(show tp)) $ return (tppos,tp,nmpos,nm)

createSignature :: P.SimpleName -> [Parameter] -> Signature
createSignature nm params = Signature nm (fmap (\(NewParameter _ tp _) -> tp) params)

constructorBody :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState ((Maybe ConstructorInvocation), [Assignment])
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
      let (tp,tppos) = P.createQName package toks
      tok <- P.satisfySimpleName
      let (name,nmpos) = P.createName tok
      fmap ([(NewParameter tppos tp name)] ++) nextParameter

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
  value <- term
  return (NewAssignment (getTermPosition variable) variable value)

data TermState = TermState {termStack :: [Term], package :: [T.Text]}

term :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
term = do
  castTerm <- optionMaybe $ try castTerm
  case castTerm of
    Just t -> return t
    Nothing -> do
      TermState {..} <- getState
      maybeParens <- optionMaybe $ P.satisfy LParens
      term' <- case maybeParens of
        Just pos -> do
          putState (TermState {termStack=[],..})
          parensTerm <- term
          P.satisfy RParens
          putState (TermState {..})
          return parensTerm
        Nothing -> do
          term <- (try objectCreationTerm <|> try variableThis <|> try fieldAccessTerm <|> try methodInvocationTerm)
          return term
      (terminator, _) <- lookAhead anyToken
      case terminator of
          Dot -> do
            TermState {termStack=termStack',..} <- getState
            P.satisfy Dot
            putState (TermState {termStack=(term':termStack'),..})
            term
          _ -> (return term')

termFromStack :: [Term] -> Term
termFromStack (t:ts) =
  case t of
    Value v -> Value v
    Application t a -> Application t a

objectCreationTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
objectCreationTerm = do
  TermState {..} <- getState
  satisfyKeyword "new"
  toks <- satisfyQualifiedName
  let (clazz,pos) = P.createQName package toks
  P.satisfy LParens
  arguments <- argumentList
  P.satisfy RParens
  return (Value (ObjectCreation pos clazz arguments))

variableThis :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
variableThis = do
  pos <- try $ satisfyKeyword "this"
  lookAhead expressionTerminator
  return (Value (Variable pos P.createNameThis))

variableTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
variableTerm = do
  tok <- P.satisfySimpleName
  let (name,pos) = P.createName tok
  lookAhead expressionTerminator
  return (Value (Variable pos name))

fieldAccessTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
fieldAccessTerm = do
  TermState {..} <- getState
  tok <- P.satisfySimpleName
  let (name,pos) = P.createName tok
  lookAhead expressionTerminator
  case termStack of
    [] -> return (Value (Variable pos name))
    (t:ts) -> do
      putState (TermState {termStack=ts,..})
      return (Application t (FieldAccess pos name))

methodInvocationTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
methodInvocationTerm = do
  TermState {..} <- getState
  tok <- P.satisfySimpleName
  let (method,pos) = P.createName tok
  P.satisfy LParens
  putState (TermState {termStack=[],..})
  arguments <- argumentList
  putState (TermState {..})
  P.satisfy RParens
  case termStack of
    [] -> parserFail "Invalid method invocation application"
    (t:ts) -> do
      putState (TermState {termStack=ts,..})
      return (Application t (MethodInvocation pos method arguments))

castTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
castTerm = do
  TermState {..} <- getState
  pos <- P.satisfy LParens
  toks <- satisfyQualifiedName
  let (clazz,_) = P.createQName package toks
  P.satisfy RParens
  term <- term
  return (Value (Cast pos clazz term))

expressionTerminator :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState SourcePos
expressionTerminator = P.satisfy Dot <|> P.satisfy Comma <|> P.satisfy Semi <|> P.satisfy RParens <|> P.satisfy Assign

satisfyIde :: (Stream s Identity (Token, SourcePos)) => Parsec s u (T.Text, SourcePos)
satisfyIde = token (\(tok, pos) -> (show tok))
                  (\(tok, pos) -> pos)
                  (\(tok, pos) -> case tok of Ide s -> Just (s,pos); _ -> Nothing)

satisfyKeyword :: (Stream s Identity (Token, SourcePos)) => String -> Parsec s u SourcePos
satisfyKeyword k = token (\(tok, pos) -> (show tok))
                         (\(tok, pos) -> pos)
                         (\(tok, pos) -> case tok of Keyword n -> if n == k then Just pos else Nothing; _ -> Nothing)

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
