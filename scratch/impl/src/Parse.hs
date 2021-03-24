module Parse where

import Control.Monad
import Control.Monad.Identity
import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as P

import Syntax

type Parse = Parsec String ()

sexp_lang :: Monad m => GenLanguageDef String () m
sexp_lang = P.LanguageDef
  { P.commentStart = "(*"
  , P.commentEnd = "*)"
  , P.commentLine = ""
  , P.nestedComments = True
  , P.identStart = identChar <|> char '.'
  , P.identLetter = identChar <|> digit <|> char '\'' <|> char '.'
  , P.opStart = mzero
  , P.opLetter = mzero
  , P.reservedNames = []
  , P.reservedOpNames = []
  , P.caseSensitive = True }
  where
    identChar :: (Monad m) => ParsecT String () m Char
    identChar = letter <|> char '-' <|> char '_' <|> char '>' <|> char '<' <|> char '=' <|> char '*' <|> char '~'

lexer :: P.GenTokenParser String () Identity
lexer = P.makeTokenParser sexp_lang

parens = P.parens lexer
reserved = P.reserved lexer
identifier = P.identifier lexer
colon = P.colon lexer
commaSep = P.commaSep lexer
semiSep = P.semiSep lexer
symbol = P.symbol lexer
comma = P.comma lexer

program = sexpList

sexpList :: Parse [ParsedSExp]
sexpList = many parsedSexp

parsedSexp :: Parse ParsedSExp
parsedSexp = ParsedSExp <$> getPosition <*> sexp
  
sexp :: Parse SExp
sexp = SEAtom <$> identifier
       <|> parens (SEList <$> sexpList)
       <?> "read error: expected an atom or an s-expression"

