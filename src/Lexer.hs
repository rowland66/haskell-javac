module Lexer
    ( Token(..)
    , TokenPos
    , tokenizeFromFile
    ) where

import Text.ParserCombinators.Parsec hiding (token, tokens)
import Text.Parsec.Char (endOfLine)
import Control.Applicative ((<*), (*>), (<$>), (<*>))
import qualified Data.Text as T

data Token = Ide T.Text
           | LBrace
           | RBrace
           | LParens
           | RParens
           | Semi
           | Dot
           | Comma
           | Assign
           | Keyword String
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
                 Just s  -> Ide $ T.pack ([fc] ++ s)
  where firstChar = ['A'..'Z'] ++ ['a'..'z'] ++ "_"
        rest      = firstChar ++ ['0'..'9']

lbrace, rbrace, lparens, rparens, semi, dot, comma, operator:: Parser TokenPos
lbrace = parseCharToken '{' LBrace
rbrace = parseCharToken '}' RBrace
lparens = parseCharToken '(' LParens
rparens = parseCharToken ')' RParens
semi = parseCharToken ';' Semi
dot = parseCharToken '.' Dot
comma = parseCharToken ',' Comma
operator = parseCharToken '=' Assign

parseCharToken :: Char -> Token -> Parser TokenPos
parseCharToken c t = do p <- getPosition; char c; return (t,p)

keywords =
  try (keyword "class" <|> keyword "extends" <|> keyword "new" <|> keyword "super" <|> keyword "this" <|> keyword "return" <|> keyword "package" <|> keyword "import")

keyword kw = do
  p <- getPosition
  k <- try (do {k' <- string kw; notFollowedBy $ oneOf (['A'..'Z'] ++ ['a'..'z'] ++ "_" ++ ['0'..'9']); return k' })
  return (Keyword k,p)

comment = do
  try (string "//")
  c <- manyTill anyChar endOfLine
  return c

token :: Parser TokenPos
token = (skipMany (comment >> (many space))) >> choice
    [ keywords
    , ide
    , lbrace
    , rbrace
    , lparens
    , rparens
    , semi
    , dot
    , comma
    , operator
    ]

tokens :: Parser [TokenPos]
tokens = spaces *> many (token <* spaces)

tokenizeFromFile :: FilePath -> IO (Either ParseError [TokenPos])
tokenizeFromFile fp = parseFromFile tokens fp
