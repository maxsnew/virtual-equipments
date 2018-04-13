module Grammar where

-- | A Program is a sequence of signature and module definitions.
newtype Program = Program { _defs :: [TopLevel] }
  deriving (Show, Read, Eq)
data TopLevel = TLSig SigDef | TLMod ModDef
  deriving (Show, Read, Eq)

nameOf :: TopLevel -> String
nameOf (TLSig sigdef) = _sigDefName sigdef
nameOf (TLMod moddef) = _modDefName moddef

type CheckingEnv = [(ModName, SigExp)]

data SigDef = SigDef { _sigDefName :: SigName
                     , _sigLambda  :: SigLambda
                     }
  deriving (Show, Read, Eq)

data SigLambda = SigLam
  { _sigLamArgs :: [(ModName, SigExp)]
  , _sigBody :: [SigDecl]
  }
  deriving (Show, Read, Eq)

-- | An expression that denotes a signature, must be the application
-- of a defined signature to concrete module arguments
type SigExp = SigApp

seapp = SigApp

data SigApp = SigApp { _sigCtor :: HOSigExp, _sigAppArgs :: [ModExp] }
  deriving (Show, Read, Eq)

-- | A Higher-order signature expression
data HOSigExp
  = SEName SigName
  | SELam SigName -- ^ just for error reporting
          SigLambda -- ^ invariant: always closed, well-formed
  deriving (Show, Read, Eq)

data ModExp
  = ModBase Bound
  -- | ModA
  deriving (Show, Read, Eq)

data ModDef = ModDef { _modDefName :: ModName
                     , _modLam :: ModLambda }
  deriving (Show, Read, Eq)

data ModLambda = ModLam
  { _modLamParams :: [(ModName, SigExp)]
  , _modOSig  :: SigExp
  , _modBody :: [ModDecl]
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

declName :: SigDecl -> String
declName (SigDeclSet name)      = name
declName (SigDeclFun name _)    = name
declName (SigDeclSpan name _ _) = name
declName (SigDeclTerm name _)   = name
declName (SigDeclAx name _ _ _) = name

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

mdeclName :: ModDecl -> String
mdeclName (ModDeclSet name _) = name
mdeclName (ModDeclFun name _ _) = name
mdeclName (ModDeclSpan name _ _ _) = name
mdeclName (ModDeclTerm name _ _ _ _) = name
mdeclName (ModDeclProof name _) = name



-- | Expression Language
-- These are the actual terms in the language, there's one for each
-- sort of judgment, including signature and module references

data SetExp = SetExp (ModDeref SetName)
  deriving (Show, Read, Eq)
data EltExp
  = EEVar EltVar
  | EEApp (ModDeref FunName) EltExp
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

data ModDeref n = ModDeref { _derefMod :: Maybe ModExp, _derefName :: n }
  deriving (Show, Read, Eq)
type SigName  = String
type ModName  = String
newtype Bound = Bound { unbound :: String }
  deriving (Show, Read, Eq, Ord)
type SetName  = String
type FunName  = String
type SpanName = String
type TermName = String
type AxName   = String

class Subst a where
  subst :: TopLevel -> a -> a

instance Subst Program where
  subst tl (Program []) = Program []
  subst tl (Program (def:rest)) =
    Program (subst tl def : rest')
    where
      rest' = if nameOf def == nameOf tl
              then rest
              else _defs $ subst tl $ Program rest

instance Subst TopLevel where
  subst tl (TLSig sigdef) = TLSig $ subst tl sigdef
  subst tl (TLMod moddef) = TLMod $ subst tl moddef

instance Subst SigDef where
  subst tl (SigDef name lam) = SigDef name $ subst tl lam
instance Subst SigLambda where
  subst tl (SigLam args bod) = SigLam new_args new_bod
    where (is_shadowed, new_args) = substArgs tl args
          new_bod = if is_shadowed then bod else map (subst tl) bod
instance Subst ModDef where
  subst tl (ModDef name lam) = ModDef name $ subst tl lam

instance Subst ModLambda where
  subst tl (ModLam params osig bod) = ModLam new_params new_osig new_bod
    where (is_shadowed, new_params) = substArgs tl params
          unlessShadowed f = if is_shadowed then id else f
          new_osig = unlessShadowed (subst tl) osig
          new_bod  = unlessShadowed (map (subst tl)) bod
  
instance Subst SigApp where
  subst tl (SigApp ho args) = SigApp (subst tl ho) (map (subst tl) args)

instance Subst HOSigExp where
  subst (TLMod mod) ho = ho
  subst tl ho@(SELam _ _) = ho -- lambdas are always closed
  subst (TLSig (SigDef defName lam)) ho@(SEName name) =
    if defName == name then SELam defName lam else ho

instance Subst ModExp where
  subst (TLSig sig) me = me
  subst (TLMod mod) me = error "substitution for modules isn't done"
instance Subst SigDecl where
  subst tl sdecl = case sdecl of
    SigDeclSet sname -> SigDeclSet sname
    SigDeclFun fname ftype -> SigDeclFun fname (subst tl ftype)
    SigDeclSpan sname e1 e2 -> SigDeclSpan sname (subst tl e1) (subst tl e2)
    SigDeclTerm tname tft -> error "term substitution isn't done not yet"
    SigDeclAx   axname tft t1 t2 -> error "axioms aren't supported yet"

instance Subst FunType where
  subst tl (FunType dom cod) = FunType (subst tl dom) (subst tl cod)

instance Subst SetExp where
  subst tl (SetExp deref) = SetExp (subst tl deref)

instance Subst EltExp where
  subst tl ee = case ee of
    EEVar v -> EEVar v
    EEApp modref ee -> EEApp (subst tl modref) (subst tl ee)

instance Subst (ModDeref n) where
  subst tl (ModDeref m n) = ModDeref (fmap (subst tl) m) n

instance Subst ModDecl where
  subst tl mdecl = case mdecl of
    ModDeclSet sname setExp -> ModDeclSet sname (subst tl setExp)
    ModDeclFun fname eltvar eltexp -> ModDeclFun fname eltvar (subst tl eltexp)

-- returns true if the binding is shadowed by one of the argument bindings
substArgs :: TopLevel -> [(ModName, SigExp)] -> (Bool, [(ModName, SigExp)])
substArgs tl args = loop tl args []
  where
    loop tl [] acc = (False, reverse acc)
    loop tl ((name, exp) : args) acc =
      if nameOf tl == name
      then (True, reverse acc ++ (name, subst tl exp) : args)
      else loop tl args ((name, subst tl exp) : acc)


-- traverse modnames
sigDeclModDerefs :: (Applicative f) => (ModDeref String -> f (ModDeref String)) -> SigDecl -> f SigDecl
sigDeclModDerefs k sdecl = case sdecl of
  SigDeclSet sname -> pure $ SigDeclSet sname
  SigDeclFun fname (FunType (SetExp dom) (SetExp cod)) ->
    (SigDeclFun fname .) . FunType <$> (SetExp <$> k dom) <*> (SetExp <$> k cod)
