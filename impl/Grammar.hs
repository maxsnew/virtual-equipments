module Grammar where

-- | A Program is a sequence of signature and module definitions.
type Program = [TopLevel]
data TopLevel = TLSig SigDef | TLMod ModDef
  deriving (Show, Read, Eq)

-- | A Signature Definition defines a name, parameterized by some
-- other signatures, and consists of a sequence of judgments
data SigDef = SigDef { _sigDefName :: SigName
                     , _sigDefArgs :: [(ModName, SigExp)]
                     , _sigDefBody :: [SigDecl]
                     }
  deriving (Show, Read, Eq)

data ModDef = ModDef { _modDefName :: ModName
                     , _modDefArgs :: [(ModName, SigExp)]
                     , _modDefSig  :: SigExp
                     , _modDefBody :: [ModDecl]
                     }
  deriving (Show, Read, Eq)

-- | A Signature Declaration can be for a set, a function, a span, a
-- span function, or an equality axiom between span functions
data SigDecl
  = SigDeclSet  SetName
  | SigDeclFun  FunName FunType
  | SigDeclSpan SpanName SetExp SetExp
  | SigDeclTerm TermName TermFunType
  | SigDeclAx   AxName TermFunType TermExp TermExp
  deriving (Show, Read, Eq)

data FunType = FunType { _dom :: SetExp, _cod :: SetExp }
  deriving (Show, Read, Eq)
-- | TODO: encode this
data TermFunType = TermFunType { _tftPrint :: String }
  deriving (Show, Read, Eq)

-- | A Module Declaration is an *instance* of a signature declaration.
data ModDecl
  = ModDeclSet SetName SetExp
  | ModDeclFun FunName EltVar EltExp -- | f(x) = e
  | ModDeclSpan SpanName EltVar EltVar SpanExp -- | M(x;y) = N
  | ModDeclTerm TermName EltVar EltVar SpanCtx TermExp -- | forall x, y. alpha(phi_1,...phi_n) = t
  | ModDeclProof AxName Proof
  deriving (Show, Read, Eq)

-- | Expression Language
-- These are the actual terms in the language, there's one for each
-- sort of judgment, including signature and module references

data SigExp = SigApp { _sigCtor :: SigName, _sigArgs :: [ModExp] }
  deriving (Show, Read, Eq)
data ModExp
  = ModBase ModName
  deriving (Show, Read, Eq)
data SetExp = SetExp (ModDeref SetName)
  deriving (Show, Read, Eq)
data EltExp = EltExp
  deriving (Show, Read, Eq)
data SpanExp
  = SpanEApp String TermExp TermExp
  deriving (Show, Read, Eq)
data TermExp = TermExp
  deriving (Show, Read, Eq)

-- | Going to figure out Proofs later
data Proof = Admit
  deriving (Show, Read, Eq)

-- | Variables and Names.

-- There are many sorts of variables and names in our language but
-- there are two distinct classes.
--
-- Variables are the free variables in the term language, specifically
-- element variables can appear in elements and spans, and span
-- element variables can appear in span elements. These are all
-- treateed *linearly*, even *ordered*.
type EltVar = String
type SpanEltVar = String
type SpanCtx = [SpanEltVar]

-- Names refer to declarations in Signatures and Modules. They are
-- treated as *cartesian* so we can define things like Functor C C and
-- the like.
-- There is one of these for every "sort" in the language, including
-- signatures and modules themselves

data ModDeref n = ModDeref { _derefMod :: ModExp, _derefName :: n }
  deriving (Show, Read, Eq)
type SigName  = String
type ModName  = String
type SetName  = String
type FunName  = String
type SpanName = String
type TermName = String
type AxName   = String

