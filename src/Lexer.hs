module Lexer
    ( Token(..)
    , TokenPos
    , tokenize
    , tokenizeFromFile
    ) where

import Text.ParserCombinators.Parsec hiding (token, tokens)
import Control.Applicative ((<*), (*>), (<$>), (<*>))

data Token = Ide String
           | LBrack
           | RBrack
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
                 Nothing -> Ide [fc]
                 Just s  -> Ide $ [fc] ++ s
  where firstChar = ['A'..'Z'] ++ ['a'..'z'] ++ "_"
        rest      = firstChar ++ ['0'..'9']

parsePos :: Parser Token -> Parser TokenPos
parsePos p = (,) <$> p <*> getPosition

lbrack, rbrack, lbrace, rbrace, lparens, rparens, semi, dot, comma :: Parser TokenPos
lbrack = parsePos $ char '[' >> return LBrack
rbrack = parsePos $ char ']' >> return RBrack
lbrace = parsePos $ char '{' >> return LBrace
rbrace = parsePos $ char '}' >> return RBrace
lparens = parsePos $ char '(' >> return LParens
rparens = parsePos $ char ')' >> return RParens
semi = parsePos $ char ';' >> return Semi
dot = parsePos $ char '.' >> return Dot
comma = parsePos $ char ',' >> return Comma

keywords =
  try (keyword "class" <|> keyword "extends" <|> keyword "new" <|> keyword "super" <|> keyword "this" <|> keyword "return")

keyword kw = do
  k <- try (do {k' <- string kw; notFollowedBy $ oneOf (['A'..'Z'] ++ ['a'..'z'] ++ "_" ++ ['0'..'9']); return k' })
  parsePos $ return (Keyword k)

operator = parsePos $ char '=' >> return Assign

token :: Parser TokenPos
token = choice
    [ keywords
    , ide
    , lbrack
    , rbrack
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

tokenize :: SourceName -> String -> Either ParseError [TokenPos]
tokenize = runParser tokens ()

tokenizeFromFile :: FilePath -> IO (Either ParseError [TokenPos])
tokenizeFromFile fp = parseFromFile tokens fp
