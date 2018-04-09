module Grammar where

-- | A Program is a sequence of signature and module definitions.
data Program = ProgMT | ProgSig SigDef Program | ProgMod ModDef Program
  deriving (Show, Read)

-- | A Signature Definition defines a name, parameterized by some
-- other signatures, and consists of a sequence of judgments
data SigDef = SigDef { _sigDefName :: SigName
                     , _sigDefArgs :: [(ModName, SigExp)]
                     , _sigDefBody :: [SigDecl]
                     }
  deriving (Show, Read)

data ModDef = ModDef { _modDefName :: ModName
                     , _modDefArgs :: [(ModName, SigExp)]
                     , _modDefSig  :: SigExp
                     , _modDefBody :: [ModDecl]
                     }

-- | A Signature Declaration can be for a set, a function, a span, a
-- span function, or an equality axiom between span functions
data SigDecl
  = SigDeclSet  SetName
  | SigDeclFun  FunName FunType
  | SigDeclSpan SpanName SetExp SetExp
  | SigDeclTerm TermName TermFunType
  | SigDeclAx   AxName TermFunType TermExp TermExp

data FunType = FunType { _dom :: SetExp, _cod :: SetExp }
-- | TODO: encode this
data TermFunType = TermFunType { }

-- | A Module Declaration is an *instance* of a signature declaration.
-- | Each one potentially includes the corresponding declaration as an
-- annotation

data ModDecl = A

data SigExp = SigExp

data SetExp = SetExp (Deref SetName)
data SpanExp
  = SpanEApp String TermExp TermExp
data TermExp = TermExp


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

-- Names refer to declarations in Signatures and Modules. They are
-- treated as *cartesian* so we can define things like Functor C C and
-- the like.
-- There is one of these for every "sort" in the language, including
-- signatures and modules themselves

data Deref n = Deref { _derefMod :: ModExp, _derefName :: n }
type SigName  = String
type ModName  = String
type SetName  = String
type FunName  = String
type SpanName = String
type TermName = String
type AxName   = String
