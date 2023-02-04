module Lexer
    ( Token(..)
    , TokenPos
    , tokenizeFromFile
    ) where

import qualified Control.Exception as E 
import System.IO
import System.Exit
import Text.ParserCombinators.Parsec hiding (token, tokens)
import Text.Parsec.Char (endOfLine)
import Control.Applicative ((<*), (*>), (<$>), (<*>))
import qualified Data.Text as T
import Data.Int (Int32)
import Debug.Trace (trace, traceShow)

data Token = Ide T.Text
           | LBrace
           | RBrace
           | LParens
           | RParens
           | LAngleBracket
           | RAngleBracket
           | Semi
           | Dot
           | Comma
           | Assign
           | Asterick
           | Colon
           | Question
           | Keyword String
           | IntegerLiteral Int32
           | StringLiteral String
           | BooleanLiteral Bool
    deriving (Show, Eq)

type TokenPos = (Token, SourcePos)

ide :: Parser TokenPos
ide = do
  pos <- getPosition
  fc  <- oneOf firstChar
  r   <- optionMaybe (many $ oneOf rest)
  spaces
  return $ flip (,) pos $ case r of
           Nothing -> Ide (T.pack [fc])
           Just s  -> Ide $ T.pack (fc : s)
  where firstChar = ['A'..'Z'] ++ ['a'..'z'] ++ "_"
        rest      = firstChar ++ ['0'..'9']

decimalNumeral :: Parser TokenPos
decimalNumeral = do
  pos <- getPosition
  fc <- oneOf nonZeroDigit
  r <- optionMaybe (many $ oneOf digit)
  spaces
  return $ flip (,) pos $ case r of
           Nothing -> IntegerLiteral (read [fc] :: Int32)
           Just s  -> IntegerLiteral (read (fc:s) :: Int32)
  where nonZeroDigit = ['1'..'9']
        digit        = ['0'..'9']

quotedString :: Parser TokenPos
quotedString = do
  pos <- getPosition
  char '"'
  r <- manyTill (escDoubleQuote <|> escTab <|> escNewLine <|> escCarriageReturn <|> escBackSlash <|> anyChar) (char '"')
  spaces
  return $ flip (,) pos $ StringLiteral r

boolean :: Parser TokenPos
boolean = do
  pos <- getPosition
  r <- try (string "true") <|> try (string "false")
  spaces
  return $ flip (,) pos $ case r of 
                            "true" -> BooleanLiteral True
                            "false" -> BooleanLiteral False
                            _ -> undefined

escDoubleQuote :: Parser Char
escDoubleQuote = fmap (const '"') (try $ string "\\\"")

escTab :: Parser Char
escTab = fmap (const '\t') (try $ string "\\t")

escNewLine :: Parser Char 
escNewLine = fmap (const '\n') (try $ string "\\n")

escCarriageReturn :: Parser Char
escCarriageReturn = fmap (const '\r') (try $ string "\\r")

escBackSlash :: Parser Char
escBackSlash = fmap (const '\\') (try $ string "\\\\")

lbrace, rbrace, lparens, rparens, langleBracket, rangleBracket, semi, dot, comma, operator, asterick, colon, question:: Parser TokenPos
lbrace = parseCharToken '{' LBrace
rbrace = parseCharToken '}' RBrace
lparens = parseCharToken '(' LParens
rparens = parseCharToken ')' RParens
langleBracket = parseCharToken '<' LAngleBracket
rangleBracket = parseCharToken '>' RAngleBracket
semi = parseCharToken ';' Semi
dot = parseCharToken '.' Dot
comma = parseCharToken ',' Comma
operator = parseCharToken '=' Assign
asterick = parseCharToken '*' Asterick
colon = parseCharToken ':' Colon
question = parseCharToken '?' Question

parseCharToken :: Char -> Token -> Parser TokenPos
parseCharToken c t = do p <- getPosition; char c; return (t,p)

comments =
  skipMany $ try (multiLineComment >> spaces) <|> try (singleLineComment >> spaces)

multiLineComment = do
  string "/*"
  manyTill anyChar (try (string "*/"))

singleLineComment = do
  string "//"
  manyTill anyChar (try endOfLine) 

keywords =
  try (keyword "class" <|> keyword "extends" <|> keyword "new" <|> keyword "super" <|> keyword "this" 
   <|> keyword "return" <|> keyword "package" <|> keyword "import" <|> keyword "abstract")

keyword kw = do
  p <- getPosition
  k <- try (do {k' <- string kw; notFollowedBy $ oneOf (['A'..'Z'] ++ ['a'..'z'] ++ "_" ++ ['0'..'9']); return k' })
  return (Keyword k,p)

literal =
  try decimalNumeral <|> quotedString <|> boolean

token :: Parser TokenPos
token = choice
    [ keywords
    , literal
    , ide
    , lbrace
    , rbrace
    , lparens
    , rparens
    , langleBracket
    , rangleBracket
    , semi
    , dot
    , comma
    , asterick
    , operator
    , colon
    , question
    ]

tokens :: Parser [TokenPos]
tokens = (spaces >> comments) *> many (token <* (spaces >> comments))

tokenizeFromFile :: FilePath -> IO (Either ParseError [TokenPos])
tokenizeFromFile fp = E.catch 
  (parseFromFile tokens fp)
  (\e -> do 
    let err = E.displayException (e :: E.IOException)
    hPutStrLn stderr ("failure reading compilation unit "++err)
    exitWith (ExitFailure 1))
