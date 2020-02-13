module Grammar where

-- | A Program is just a module
type Program = ModuleBody

-- | A Module is a sequence of statements
newtype ModuleBody = ModuleBody { _defs :: [Decl ScopedExp] }
  deriving (Show, Read, Eq)

-- | A statement is a definition of a signature, module or term or an
-- assertion of an equality (between transformations?)
data ScopedExp
  = ScSig SigExp
  | ScModule ModExp
  | ScSet SetExp
  | ScFun ScopedEltExp
  | ScSpan ScopedSpanExp
  | ScTrans ScopedTransExp
  | ScAssert ScopedProofExp
  deriving (Show, Read, Eq)

data Decl a = Decl { _name :: String , _defn :: a }
  deriving (Show, Read, Eq)
  
type Ctx = [Decl ScopedExp]

-- First order lambda calculus
data SigExp
  = SigBase GroundSigExp
  | SigApp GroundSigExp [Exp]
  deriving (Show, Read, Eq)

data GroundSigExp
  = GSigVar String
  | GSigLam SigLambda
  deriving (Show, Read, Eq)

data SigLambda = SigLam
  { _sigLamArgs :: [Decl Generator]
  , _sigBody :: [Decl Generator]
  }
  deriving (Show, Read, Eq)

data Generator
  = GenMod SigExp -- "abstract module"
  | GenSet -- "base type"
  | GenFun EltTy -- "function symbol"
  | GenSpan SpanTy -- "base type constructor"
  | GenTrans TransTy -- "function symbol"
  | GenEq EqTy -- "axiom"
  deriving (Show, Read, Eq)

data ModDeref
  = MDCurMod String
  | MDSelect ModExp [String]
  deriving (Show, Read, Eq)

data Exp
  = ERef ModDeref -- after type checking this shouldn't be possible,
                  -- because it must be resolved to be one of the
                  -- following other kinds of expr
  | EMod ModExp
  | ESet SetExp
  | EElt EltExp
  | ESpan SpanExp
  | ETrans TransExp
  | EProof ProofExp
  deriving (Show, Read, Eq)

-- exactly the same as signature structure. Abstract over it?
data ModExp
  = ModBase GroundModExp
  | ModApp GroundModExp [Exp]
  deriving (Show, Read, Eq)

data GroundModExp
  = GModVar ModDeref
  | GModLam ModLambda
  deriving (Show, Read, Eq)

data ModLambda = ModLam
  { _modLamParams :: [Decl Generator]
  , _modOSig  :: SigExp
  , _modBody :: ModuleBody
  }
  deriving (Show, Read, Eq)

-- | Expression Language
-- These are the actual terms in the language, there's one for each
-- sort of judgment, including signature and module references.
-- with them we define the "scoped" version of each, which is the
-- version used in a definition

data SetExp
  = SetDeref ModDeref
  deriving (Show, Read, Eq)

data EltExp
  = EEVar String
  | EEApp ModDeref EltExp
  deriving (Show, Read, Eq)

data TypedEltVar
  = TypedEltVar { _eltvar :: String, _eltvarty :: SetExp }
  deriving (Show, Read, Eq)

data EltScope
  = EltScope { _eltinp :: TypedEltVar, _eltty :: SetExp }
  deriving (Show, Read, Eq)

type EltTy = (SetExp, SetExp)

type ScopedEltExp = (EltScope, EltExp)

data SpanExp
  = SpanEApp ModDeref EltExp EltExp
  deriving (Show, Read, Eq)

data SpanScope
  = SpanScope { _spancontra :: TypedEltVar, _spancovar :: TypedEltVar }
  deriving (Show, Read, Eq)

type ScopedSpanExp = (SpanScope, SpanExp)

type SpanTy = (SetExp, SetExp)

data TransExp = TransExp -- TODO
  deriving (Show, Read, Eq)

data TransScope = TransScope
  deriving (Show, Read, Eq)

type ScopedTransExp = (TransScope, TransExp)

type TransTy = ()

-- | Going to figure out Proofs later
data ProofExp = Assert
  deriving (Show, Read, Eq)

type EqScope = ()
type ScopedProofExp = ()
type EqTy = ()
-- -- | Variables and Names.
-- --
-- -- Variables are the free variables in the term language, specifically
-- -- element variables can appear in elements and spans, and span
-- -- element variables can appear in span elements. These are all
-- -- treateed *linearly*, even *ordered*.
-- type EltVar = String
-- type SpanEltVar = String
-- type SpanCtx = [SpanEltVar]

-- -- Names refer to declarations in Signatures and Modules. They are
-- -- treated as *cartesian* so we can define things like Functor C C and
-- -- the like.
-- -- There is one of these for every "sort" in the language, including
-- -- signatures and modules themselves

-- data ModDeref n = ModDeref { _derefMod :: Maybe ModExp, _derefName :: n }
--   deriving (Show, Read, Eq)
-- type SigName  = String
-- type ModName  = String
-- newtype Bound = Bound { unbound :: String }
--   deriving (Show, Read, Eq, Ord)
-- type SetName  = String
-- type FunName  = String
-- type SpanName = String
-- type TermName = String
-- type AxName   = String

-- class Subst a where
--   subst :: TopLevel -> a -> a

-- instance Subst Program where
--   subst tl (Program []) = Program []
--   subst tl (Program (def:rest)) =
--     Program (subst tl def : rest')
--     where
--       rest' = if nameOf def == nameOf tl
--               then rest
--               else _defs $ subst tl $ Program rest

-- instance Subst TopLevel where
--   subst tl (TLSig sigdef) = TLSig $ subst tl sigdef
--   subst tl (TLMod moddef) = TLMod $ subst tl moddef

-- instance Subst SigDef where
--   subst tl (SigDef name lam) = SigDef name $ subst tl lam
-- instance Subst SigLambda where
--   subst tl (SigLam args bod) = SigLam new_args new_bod
--     where (is_shadowed, new_args) = substArgs tl args
--           new_bod = if is_shadowed then bod else map (subst tl) bod
-- instance Subst ModDef where
--   subst tl (ModDef name lam) = ModDef name $ subst tl lam

-- instance Subst ModLambda where
--   subst tl (ModLam params osig bod) = ModLam new_params new_osig new_bod
--     where (is_shadowed, new_params) = substArgs tl params
--           unlessShadowed f = if is_shadowed then id else f
--           new_osig = unlessShadowed (subst tl) osig
--           new_bod  = unlessShadowed (map (subst tl)) bod
  
-- instance Subst SigApp where
--   subst tl (SigApp ho args) = SigApp (subst tl ho) (map (subst tl) args)

-- instance Subst HOSigExp where
--   subst (TLMod mod) ho = ho
--   subst tl ho@(SELam _ _) = ho -- lambdas are always closed
--   subst (TLSig (SigDef defName lam)) ho@(SEName name) =
--     if defName == name then SELam defName lam else ho

-- instance Subst ModExp where
--   subst (TLSig sig) me = me
--   subst (TLMod mod) me = error "substitution for modules isn't done"
-- instance Subst SigDecl where
--   subst tl sdecl = case sdecl of
--     SigDeclSet sname -> SigDeclSet sname
--     SigDeclFun fname ftype -> SigDeclFun fname (subst tl ftype)
--     SigDeclSpan sname e1 e2 -> SigDeclSpan sname (subst tl e1) (subst tl e2)
--     SigDeclTerm tname tft -> error "term substitution isn't done not yet"
--     SigDeclAx   axname tft t1 t2 -> error "axioms aren't supported yet"

-- instance Subst FunType where
--   subst tl (FunType dom cod) = FunType (subst tl dom) (subst tl cod)

-- instance Subst SetExp where
--   subst tl (SetExp deref) = SetExp (subst tl deref)

-- instance Subst EltExp where
--   subst tl ee = case ee of
--     EEVar v -> EEVar v
--     EEApp modref ee -> EEApp (subst tl modref) (subst tl ee)

-- instance Subst SpanExp where
--   subst tl se = case se of
--     SpanEApp spanref coe contrae -> SpanEApp (subst tl spanref) (subst tl coe) (subst tl contrae)

-- instance Subst (ModDeref n) where
--   subst tl (ModDeref m n) = ModDeref (fmap (subst tl) m) n

-- instance Subst ModDecl where
--   subst tl mdecl = case mdecl of
--     ModDeclSet sname setExp -> ModDeclSet sname (subst tl setExp)
--     ModDeclFun fname eltvar eltexp -> ModDeclFun fname eltvar (subst tl eltexp)
--     ModDeclSpan sname covar contravar spanexp -> ModDeclSpan sname covar contravar (subst tl spanexp)

-- -- returns true if the binding is shadowed by one of the argument bindings
-- substArgs :: TopLevel -> [(ModName, SigExp)] -> (Bool, [(ModName, SigExp)])
-- substArgs tl args = loop tl args []
--   where
--     loop tl [] acc = (False, reverse acc)
--     loop tl ((name, exp) : args) acc =
--       if nameOf tl == name
--       then (True, reverse acc ++ (name, subst tl exp) : args)
--       else loop tl args ((name, subst tl exp) : acc)


-- -- traverse modnames
-- sigDeclModDerefs :: (Applicative f) => (ModDeref String -> f (ModDeref String)) -> SigDecl -> f SigDecl
-- sigDeclModDerefs k sdecl = case sdecl of
--   SigDeclSet sname -> pure $ SigDeclSet sname
--   SigDeclFun fname (FunType (SetExp dom) (SetExp cod)) ->
--     SigDeclFun fname <$> (FunType <$> (SetExp <$> k dom) <*> (SetExp <$> k cod))
--   SigDeclSpan sname (SetExp coset) (SetExp contraset) -> SigDeclSpan sname <$> (SetExp <$> (k coset)) <*> (SetExp <$> (k contraset))

-- sigDeclSetExps :: Applicative f => (SetExp -> f SetExp) -> SigDecl -> f SigDecl
-- sigDeclSetExps k sdecl = case sdecl of
--   og@(SigDeclSet _) -> pure og
--   SigDeclFun fname (FunType dom cod) -> SigDeclFun fname <$> (FunType <$> k dom <*> k cod)
--   SigDeclSpan sname covar contravar -> SigDeclSpan sname <$> k covar <*> k contravar
  
-- -- modDeclSetExps :: Applicative f => (SetExp -> f SetExp) -> ModDecl -> f ModDecl
-- -- modDeclSetExps k mdecl = case mdecl of
-- --   ModDeclSet name exp -> ModDeclSet name <$> k exp
-- --   ModDeclFun f var elt -> _
