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
  { P.commentStart = "(*"
  , P.commentEnd = "*)"
  , P.commentLine = ""
  , P.nestedComments = True
  , P.identStart = identChar
  , P.identLetter = identChar <|> digit <|> char '\''
  , P.opStart = mzero
  , P.opLetter = mzero
  , P.reservedNames = ["module", "signature", "where", "set", "span", "fun", "term", "trans",
                       "def-sig", "def-mod", "def-set", "def-fun", "def-span", "def-trans", "def-proof",
                       "." ]
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
comma = P.comma lexer

program :: Parse Program
program = ModuleBody <$> moduleBody

moduleBody :: Parse [Decl ScopedExp]
moduleBody = many modulDecl

modulDecl :: Parse (Decl ScopedExp)
modulDecl
  = decl "def-sig" (ScSig <$> sigExp)
  <|> decl "def-mod" (ScModule <$> modExp)
  <|> decl "def-set" (ScSet <$> setExp)
  <|> decl "def-fun" (ScFun <$> scopedEltExp)
  <|> decl "def-span" (ScSpan <$> scopedSpanExp)
  <|> decl "def-trans" (ScTrans <$> scopedTransExp)
  <|> decl "def-proof" (ScAssert <$> scopedProofExp)

decl :: String -> Parse a -> Parse (Decl a)
decl defA parseA = parens $ reserved defA >>
  Decl <$> identifier <*> parseA

sigExp :: Parse SigExp
sigExp =
  SigBase <$> groundSigExp
  <|> (parens $ SigApp <$> groundSigExp <*> many anyExp)
  where
    groundSigExp :: Parse GroundSigExp
    groundSigExp = GSigVar <$> identifier <|> sigLam
    -- (sigule ((X set) ...) S
    --   (def-set Y X)
    --   ...)
    sigLam :: Parse GroundSigExp
    sigLam
      = GSigLam <$> (parens $ (reserved "sig" >>
         SigLam <$> parens (many generator) <*> (many generator)))

modExp :: Parse ModExp
modExp =
  ModBase <$> groundModExp
  <|> (parens $ ModApp <$> groundModExp <*> many anyExp)
  where
    groundModExp :: Parse GroundModExp
    groundModExp = GModVar <$> modDeref <|> modLam
    -- (module ((X set) ...) S
    --   (def-set Y X)
    --   ...)
    modLam :: Parse GroundModExp
    modLam
      = GModLam <$> (parens $ (reserved "module" >>
         ModLam <$> parens (many generator) <*> sigExp <*> (ModuleBody <$> moduleBody)))

generator :: Parse (Decl Generator)
generator
  =   genName "module" (GenMod <$> sigExp)
  <|> genName "set" (pure GenSet)
  <|> genName "fun" (GenFun <$> eltTy)
  <|> genName "span" (GenSpan <$> spanTy)
  <|> genName "trans" (GenTrans <$> transTy)
  <|> genName "axiom" (GenEq <$> eqTy)
  where genName nameA parseA = parens $ reserved nameA >>
          Decl <$> identifier <*> parseA

        eltTy = (,) <$> setExp <*> setExp
        spanTy = (,) <$> setExp <*> setExp
        transTy = pure ()
        eqTy = pure ()

  -- | GenSet -- "base type"                        (set X)
  -- | GenFun EltScope -- "function symbol"         (fun f A B)
  -- | GenSpan SpanScope -- "base type constructor" (span R A B)
  -- | GenTrans TransScope -- "function symbol"     (fun f Phi R)
  -- | GenEq EqScope -- "axiom"                     (axiom p t u)

anyExp :: Parse Exp
anyExp = _
            
setExp = SetDeref <$> modDeref -- C.Ob

  
-- ((x S) S' t)

typedEltVar = (parens $ TypedEltVar <$> identifier <*> setExp)

scopedEltExp :: Parse ScopedEltExp
scopedEltExp = (,) <$> eltScope <*> eltExp
  where
    eltScope :: Parse EltScope
    eltScope = EltScope <$> typedEltVar <*> setExp

eltExp :: Parse EltExp
eltExp = (EEVar <$> identifier)
  <|> (parens $ EEApp <$> modDeref <*> eltExp)

-- ((x S) (y S') M)
scopedSpanExp :: Parse ScopedSpanExp
scopedSpanExp = (,)  <$> spanScope <*> spanExp
  where spanScope = SpanScope <$> typedEltVar <*> typedEltVar

spanExp = parens $
  SpanEApp <$> modDeref <*> eltExp <*> eltExp

scopedTransExp :: Parse ScopedTransExp
scopedTransExp = fail "NYE"


scopedProofExp = fail "NYE"

modDeref :: Parse ModDeref
modDeref = (MDCurMod <$> identifier)
  <|> (parens $ reserved "." >>
       MDSelect <$> modExp <*> many identifier)

-- signature :: Parse SigDef
-- signature = do
--   reserved "signature"
--   (name, args) <- multi_app sigName parameter
--   reserved "where"
--   bod  <- semiSep sigdecl
--   reserved "end"
--   return $ SigDef name (SigLam args bod)

-- parameter :: Parse (ModName, SigExp)
-- parameter = do
--   name <- identifier
--   colon
--   sig  <- sigExp
--   return (name, sig)

-- sigExp :: Parse SigExp
-- sigExp = uncurry seapp <$> multi_app (SEName <$> sigName) modulExp

-- sigName :: Parse SigName
-- sigName = identifier

-- modulExp :: Parse ModExp
-- modulExp = ModBase <$> (Bound <$> identifier)

-- multi_app :: Parse n -> Parse arg -> Parse (n, [arg])
-- multi_app nameP argP = (,) <$> nameP <*> parens (commaSep argP)

-- sigdecl :: Parse SigDecl
-- sigdecl
--   =   reserved "set"   *> (SigDeclSet <$> setName)
--   <|> reserved "fun"   *> (SigDeclFun <$> (funName <* colon) <*> funType)
--   <|> reserved "span"  *> (SigDeclSpan <$> (spanName <* colon) <*> (setExp <* twiddle) <*> setExp)
--   -- <|> reserved "term"  *> (SigDeclTerm <$> _)
--   -- <|> reserved "axiom" *> (SigDeclAx <$> _)
--   where
--     funType = FunType <$> (setExp <* symbol "->") <*> setExp
--     twiddle = symbol "~~"

-- moddecl :: Parse ModDecl
-- moddecl
--   =   reserved "set" *> (ModDeclSet <$> setName <* symbol "=" <*> setExp)
--   <|> reserved "fun" *> (ModDeclFun <$> funName <*> parens eltVar <* symbol "=" <*> eltExp)
--   <|> reserved "span" *> modDeclSpan
--   where
--     modDeclSpan = do
--       name <- spanName
--       (covar, contravar) <- twoArgs eltVar
--       symbol "="
--       sexp <- spanExp
--       return $ ModDeclSpan name covar contravar sexp
-- setExp :: Parse SetExp
-- setExp
--   = SetExp <$> modDeref setName

-- eltExp :: Parse EltExp
-- eltExp
--   = try (EEApp <$> (modDeref funName) <*> parens eltExp)
--   <|> EEVar <$> eltVar

-- twoArgs :: Parse a -> Parse (a, a)
-- twoArgs p = parens $ (,) <$> (p <* comma) <*> p

-- spanExp :: Parse SpanExp
-- spanExp = uncurSpanEApp <$> modDeref spanName <*> twoArgs eltExp
--   where uncurSpanEApp x (y,z) = SpanEApp x y z

-- modDeref :: Parse n -> Parse (ModDeref n)
-- modDeref nP = try derefExp <|> litExp
--   where
--     derefExp = ModDeref <$> (Just <$> modulExp) <*> (char '.' *> nP)
--     litExp = ModDeref Nothing <$> nP


-- modName :: Parse ModName
-- modName = identifier
-- setName :: Parse SetName
-- setName = identifier
-- funName :: Parse FunName
-- funName = identifier
-- spanName :: Parse SpanName
-- spanName = identifier
-- termName :: Parse TermName
-- termName = identifier
-- axName :: Parse AxName
-- axName = identifier

-- eltVar :: Parse EltVar
-- eltVar = identifier
