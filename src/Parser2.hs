{-# LANGUAGE FlexibleContexts #-}

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
import Data.List (intersperse)
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.Parsec.Pos
import Text.Parsec.Error
import qualified Parser as P
import Lexer
import Debug.Trace

data Abstraction = FieldAccess SourcePos String
                 | MethodInvocation SourcePos String [Term]
                 deriving Show

data Value = Variable SourcePos String
          | ObjectCreation SourcePos DataType [Term]
          | Cast SourcePos DataType Term
          deriving Show

data Term = Value Value | Application Term Abstraction deriving Show

getTermPosition :: Term -> SourcePos
getTermPosition (Value (Variable pos _)) = pos
getTermPosition (Value (ObjectCreation pos _ _)) = pos
getTermPosition (Value (Cast pos _ _)) = pos
getTermPosition (Application t _) = getTermPosition t

type DataType = String;

data SourcePos' = SourcePos' SourcePos | CompiledCode

data Extends = NewExtends SourcePos String | ExtendsObject deriving Show

data ConstructorInvocation = NewConstructorInvocation SourcePos [Term] deriving Show

data Assignment = NewAssignment SourcePos Term Term deriving Show

data Signature = Signature String [DataType]

data Parameter = NewParameter SourcePos DataType String deriving Show

data Field = NewField SourcePos DataType SourcePos String

data Constructor = NewConstructor SourcePos' [Parameter] Signature (Maybe ConstructorInvocation) [Assignment]

data Method = NewMethod SourcePos String [Parameter] DataType Signature Term deriving Show

data Clazz2 = NewClazz2 SourcePos' String Extends [Field] [Constructor] [Method]

{-- Parameters are equal if their types are equal. This is convenient in some cases, but might cause problems in others -}
instance Eq Parameter where
  (==) (NewParameter _ tp1 _) (NewParameter _ tp2 _) = (tp1 == tp2)

instance Show Signature where
  show (Signature nm types) = nm ++ "(" ++ (concat (intersperse "," types)) ++ ")"

instance Eq Signature where
  (==) (Signature nm1 types1) (Signature nm2 types2) = (nm1 == nm2) && (types1 == types2)

instance Show Field where
  show (NewField _ tp _ nm) = tp ++ " " ++ nm ++ ";"

instance Show Constructor where
  show (NewConstructor _ _ sig _ assignments) = (show sig)++"\n"++(foldr (\a str -> str++"\n"++(show a)) "" assignments)

instance Show Clazz2 where
  show (NewClazz2 _ nm extends fields constructors methods) =
    "class " ++ nm ++ " " ++ (show extends) ++ "\n" ++
      (foldr (\f str -> (show f)++"\n"++str) "" fields) ++
      foldr (\c str -> (show c)++"\n"++str) "" constructors

getClazz2Name :: Clazz2 -> String
getClazz2Name (NewClazz2 _ nm _ _ _ _) = nm

parseClasses2 :: (Map.Map String P.Clazz) -> (Either ParseError (Map.Map String Clazz2))
parseClasses2 clazzMap = trace "Parser2" $ sequence (fmap (\cls -> mapClazz cls clazzMap) clazzMap)

mapClazz :: P.Clazz -> (Map.Map String P.Clazz) -> Either ParseError Clazz2
mapClazz (P.NewClazz pos name maybeExtends fields constructors methods) classMap = do
  e <- case maybeExtends of Just tok -> (mapExtends classMap tok); Nothing -> Right ExtendsObject;
  f <- sequence (fmap (mapField classMap) fields)
  c <- sequence (fmap (mapConstructor classMap) constructors)
  m <- sequence (fmap (mapMethod classMap) methods)
  return (NewClazz2 (SourcePos' pos) name e f c m)

mapExtends :: (Map.Map String P.Clazz) -> TokenPos -> Either ParseError Extends
mapExtends classMap tok = runParser parseExtends (TermState classMap []) "" [tok]

mapField :: (Map.Map String P.Clazz) -> P.Field -> Either ParseError Field
mapField classMap (P.NewField toks) = do
  (tppos,tp,nmpos,nm) <- runParser parseField (TermState classMap []) "" toks
  return (NewField tppos tp nmpos nm)

mapConstructor :: (Map.Map String P.Clazz) -> P.Constructor -> Either ParseError Constructor
mapConstructor classMap (P.NewConstructor pos toks (P.NewBody bodyToks)) = do
  params <- runParser parameter (TermState classMap []) "" toks
  (super, assignments) <- runParser constructorBody (TermState classMap []) "" bodyToks
  return (NewConstructor (SourcePos' pos) params (createSignature "<init>" params) super assignments)

mapMethod :: (Map.Map String P.Clazz) -> P.Method -> Either ParseError Method
mapMethod classMap (P.NewMethod tpTok nmTok paramsToks (P.NewBody bodyToks)) = do
  (tp,_) <- runParser satisfyTypeIde (TermState classMap []) "" tpTok
  (nm,pos) <- runParser satisfyIde (TermState classMap []) "" [nmTok]
  params <- runParser parameter (TermState classMap []) "" paramsToks
  body <- runParser methodBody (TermState classMap []) "" bodyToks
  return (NewMethod pos nm params tp (createSignature nm params) body)

parseExtends :: (Stream s Identity TokenPos) => Parsec s TermState Extends
parseExtends = do
  (clazz,pos) <- satisfyTypeIde
  return (if (clazz == "Object") then ExtendsObject else (NewExtends pos clazz))

parseField :: (Stream s Identity TokenPos) => Parsec s TermState (SourcePos, DataType, SourcePos, String)
parseField = do
  (tp,tppos) <- satisfyTypeIde
  (nm,nmpos) <- satisfyIde
  return (tppos,tp,nmpos,nm)

createSignature :: String -> [Parameter] -> Signature
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
      (tp,tppos) <- satisfyTypeIde
      (name,nmpos) <- satisfyIde
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

data TermState = TermState (Map.Map String P.Clazz) [Term]

term :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
term = do
  castTerm <- optionMaybe $ try castTerm
  case castTerm of
    Just t -> return t
    Nothing -> do
      TermState classMap termStack <- getState
      maybeParens <- optionMaybe $ P.satisfy LParens
      term' <- case maybeParens of
        Just pos -> do
          putState (TermState classMap [])
          parensTerm <- term
          P.satisfy RParens
          putState (TermState classMap termStack)
          return parensTerm
        Nothing -> do
          term <- (try objectCreationTerm <|> try variableThis <|> try fieldAccessTerm <|> try methodInvocationTerm)
          return term
      (terminator, _) <- lookAhead anyToken
      case terminator of
          Dot -> do
            TermState classMap termStack' <- getState
            P.satisfy Dot
            putState (TermState classMap (term':termStack'))
            term
          _ -> (return term')

termFromStack :: [Term] -> Term
termFromStack (t:ts) =
  case t of
    Value v -> Value v
    Application t a -> Application t a

objectCreationTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
objectCreationTerm = do
  satisfyKeyword "new"
  (clazz,pos) <- satisfyTypeIde
  P.satisfy LParens
  arguments <- argumentList
  P.satisfy RParens
  return (Value (ObjectCreation pos clazz arguments))

variableThis :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
variableThis = do
  pos <- try $ satisfyKeyword "this"
  lookAhead expressionTerminator
  return (Value (Variable pos "this"))

variableTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
variableTerm = do
  (name,pos) <- satisfyIde
  lookAhead expressionTerminator
  return (Value (Variable pos name))


fieldAccessTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
fieldAccessTerm = do
  TermState classMap termStack <- getState
  (name,pos) <- satisfyIde
  lookAhead expressionTerminator
  case termStack of
    [] -> return (Value (Variable pos name))
    (t:ts) -> do
      putState (TermState classMap ts)
      return (Application t (FieldAccess pos name))

methodInvocationTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
methodInvocationTerm = do
  TermState classMap termStack <- getState
  (method,pos) <- satisfyIde
  P.satisfy LParens
  putState (TermState classMap [])
  arguments <- argumentList
  putState (TermState classMap termStack)
  P.satisfy RParens
  case termStack of
    [] -> parserFail "Invalid method invocation application"
    (t:ts) -> do
      putState (TermState classMap ts)
      return (Application t (MethodInvocation pos method arguments))

castTerm :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState Term
castTerm = do
  pos <- P.satisfy LParens
  (clazz,_) <- satisfyTypeIde
  P.satisfy RParens
  term <- term
  return (Value (Cast pos clazz term))

expressionTerminator :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState SourcePos
expressionTerminator = P.satisfy Dot <|> P.satisfy Comma <|> P.satisfy Semi <|> P.satisfy RParens <|> P.satisfy Assign

satisfyTypeIde :: (Stream s Identity (Token, SourcePos)) => Parsec s TermState (String, SourcePos)
satisfyTypeIde = do
  first <- satisfyIde
  satisfyTypeIde' first

satisfyTypeIde' :: (Stream s Identity (Token, SourcePos)) => (String, SourcePos) -> Parsec s TermState (String, SourcePos)
satisfyTypeIde' (first, pos) = do
  maybeDot <- optionMaybe (P.satisfy Dot)
  case maybeDot of
    Just _ -> do
      (next,_) <- satisfyIde
      satisfyTypeIde' (first++"/"++next, pos)
    Nothing -> return (first, pos)

satisfyIde :: (Stream s Identity (Token, SourcePos)) => Parsec s u (String, SourcePos)
satisfyIde = token (\(tok, pos) -> (show tok))
                  (\(tok, pos) -> pos)
                  (\(tok, pos) -> case tok of Ide s -> Just (s,pos); _ -> Nothing)

satisfyKeyword :: (Stream s Identity (Token, SourcePos)) => String -> Parsec s u SourcePos
satisfyKeyword k = token (\(tok, pos) -> (show tok))
                         (\(tok, pos) -> pos)
                         (\(tok, pos) -> case tok of Keyword n -> if n == k then Just pos else Nothing; _ -> Nothing)
