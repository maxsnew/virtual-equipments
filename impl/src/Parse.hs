module Parse where

import Control.Monad
import Control.Monad.Identity
import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as P

import Grammar

type Parse = Parsec String ()

sexp_lang :: Monad m => GenLanguageDef String () m
sexp_lang = P.LanguageDef
  { P.commentStart = ""
  , P.commentEnd = ""
  , P.commentLine = "--"
  , P.nestedComments = False
  , P.identStart = identChar
  , P.identLetter = identChar
  , P.opStart = mzero
  , P.opLetter = mzero
  , P.reservedNames = ["module", "signature", "where", "end", "set", "span", "fun", "term"]
  , P.reservedOpNames = []
  , P.caseSensitive = True }
  where
    identChar = letter <|> char '-' <|> char '_'

lexer :: P.GenTokenParser String () Identity
lexer = P.makeTokenParser sexp_lang

parens = P.parens lexer
reserved = P.reserved lexer
identifier = P.identifier lexer
colon = P.colon lexer
commaSep = P.commaSep lexer
semiSep = P.semiSep lexer
symbol = P.symbol lexer

program :: Parse Program
program = many (TLSig <$> signature <|> TLMod <$> modul)

signature :: Parse SigDef
signature = do
  reserved "signature"
  (name, args) <- multi_app sigName parameter
  reserved "where"
  bod  <- semiSep sigdecl
  reserved "end"
  return $ SigDef name args bod

modul :: Parse ModDef
modul = do
  reserved "module"
  (name, args) <- multi_app modName parameter
  colon
  osig <- sigExp
  reserved "where"
  bod <- semiSep moddecl
  reserved "end"
  return $ ModDef name args osig bod
  
parameter :: Parse (ModName, SigExp)
parameter = do
  name <- identifier
  colon
  sig  <- sigExp
  return (name, sig)

sigExp :: Parse SigExp
sigExp = uncurry SigApp <$> multi_app sigName modulExp

sigName :: Parse SigName
sigName = identifier

modulExp :: Parse ModExp
modulExp = ModBase <$> identifier

multi_app :: Parse n -> Parse arg -> Parse (n, [arg])
multi_app nameP argP = (,) <$> nameP <*> parens (commaSep argP)

sigdecl :: Parse SigDecl
sigdecl
  =   reserved "set"   *> (SigDeclSet <$> setName)
  <|> reserved "fun"   *> (SigDeclFun <$> (funName <* colon) <*> funType)
  -- <|> reserved "span"  *> (SigDeclSpan <$> _ <*>  _ <*> _)
  -- <|> reserved "term"  *> (SigDeclTerm <$> _)
  -- <|> reserved "axiom" *> (SigDeclAx <$> _)
  where
    funType = FunType <$> (setExp <* symbol "->") <*> setExp

moddecl :: Parse ModDecl
moddecl = mzero

setExp :: Parse SetExp
setExp
  = SetExp <$> (try derefExp <|> litExp)
  where
    derefExp = ModDeref <$> (Just <$> modulExp) <*> (char '.' *> identifier)
    litExp = ModDeref Nothing <$> identifier

modName :: Parse ModName
modName = identifier
setName :: Parse SetName
setName = identifier
funName :: Parse FunName
funName = identifier
spanName :: Parse SpanName
spanName = identifier
termName :: Parse TermName
termName = identifier
axName :: Parse AxName
axName = identifier
  
