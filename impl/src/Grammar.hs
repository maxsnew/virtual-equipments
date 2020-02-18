{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
module Grammar where

import qualified Text.Parsec as Parsec

-- | Raw S-expressions, the output of the parser.
data ParsedSExp = ParsedSExp { _loc :: Parsec.SourcePos, _sexp :: SExp }
  deriving (Show)

data SExp
  = SEAtom String
  | SEList [ParsedSExp]
  deriving (Show)

-- | A Program is just a module body
type Program = ModuleBody

-- | A Module is a sequence of definitions
newtype ModuleBody = ModuleBody { _defs :: [SynDecl ScopedExp] }
  deriving (Show, Read, Eq)

-- | A definition is a definition of a signature, module or term or an
-- assertion of an equality (between transformations?)
data ScopedExp
  = ScSig SigExp
  | ScMod ModExp
  | ScSet SetExp
  | ScFun ScopedEltExp
  | ScSpan ScopedSpanExp
  | ScTrans ScopedTransExp
  | ScAssert ScopedProofExp
  deriving (Show, Read, Eq)

data Decl name a = Decl { _name :: name , _defn :: a }
  deriving (Show, Read, Eq, Functor)

type SynDecl = Decl String

type Ctx = [SynDecl SemVal]

-- | 
data SemVal
  = SemSet SetNF
  | SemFun SetNF -- domain set
           SetNF -- codomain set
           (EltNF -> EltNF) -- Yoneda-embedding of the term
  | SemSpan SetNF -- contravariant dependency
            SetNF -- covariant dependency
            (EltNF -> EltNF -> SpanNF) -- Yoneda embedding of the term
-- | SemTrans ??
-- | SemProof ??
  -- | SemSig -- TODO
  | SemMod -- TODO

type SetNF = DBRef
data EltNF
  = ENFId
  | ENFFunApp DBRef EltNF
  deriving (Show, Eq)

data SpanNF = SNFSpanApp { _spanSymb :: DBRef, _contraElt :: EltNF, _covarElt :: EltNF }
  deriving (Show, Eq)

-- A context
-- data NForGen
--   = NGNF  ScopedNF
--   | NGGen Generator

lookupDecl :: (Eq name) => name -> [Decl name a] -> Maybe a
lookupDecl s xs = lookup s (map declToPair xs)
  where
    declToPair :: Decl name a -> (name, a)
    declToPair d = (_name d, _defn d)

-- isSig :: NForGen -> Bool
-- isSig (DGExp (ScSig _)) = True
-- isSig _                 = False

-- isMod :: NForGen -> Bool
-- isMod (DGExp (ScMod _)) = True
-- isMod (DGGen (GenMod _))    = True
-- isMod _                 = False

-- isSet :: NForGen -> Bool
-- isSet (DGExp (ScSet _)) = True
-- isSet (DGGen GenSet)    = True
-- isSet _                 = False

-- getFunTy :: NForGen -> Maybe EltTy
-- getFunTy (DGExp (ScFun scoped)) = return . eltScopeToTy . _eltscope $ scoped
-- getFunTy (DGGen (GenFun ty)) = return $ ty
-- getFunTy _ = Nothing

-- | Semantic Signature Values.
--   going to use HOAS
--   either a ground signature,
--   or parameterized by a specific type of
--   term (which includes modules)
-- data SigVal
--   = SVSig [Decl Generator]
--   | SVPSet (SetVal -> SigVal)
  -- | FunVal -> SigVal
  -- | SpanVal -> SigVal
  -- | TransVal -> SigVal
  -- 
  

data SigExp
  = SigBase GroundSigExp
  | SigApp GroundSigExp [AnyExp]
  deriving (Show, Read, Eq)

-- This seems wrong
type SigVal = [SynDecl Generator]

data GroundSigExp
  = GSigVar String
  | GSigVal SigVal
  | GSigLam SigLambda
  deriving (Show, Read, Eq)

data SigLambda = SigLam
  { _sigLamArgs :: [SynDecl Generator]
  , _sigBody :: [SynDecl Generator]
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

-- | equivalent to NEListof Int, but more useful for recursion
data DBRef
  = DBCurMod { _curMod :: Int }
  | DBSubMod { _curMod :: Int , _subMod :: DBRef }
  deriving (Show, Eq)

data AnyExp
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
  | ModApp GroundModExp [AnyExp]
  deriving (Show, Read, Eq)

data GroundModExp
  = GModVar ModDeref
  | GModLam ModLambda
  deriving (Show, Read, Eq)

data ModLambda = ModLam
  { _modLamParams :: [SynDecl Generator]
  , _modOSig      :: [SynDecl Generator]
  , _modBody :: ModuleBody
  }
  deriving (Show, Read, Eq)

-- | Expression Language
-- These are the actual terms in the language, there's one for each
-- sort of judgment, including signature and module references.
-- with them we define the "scoped" version of each, which is the
-- version used in a definition

type SetExp = ModDeref

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

data EltTy = EltTy { _eltdomty :: SetExp, _eltcodty :: SetExp }
  deriving (Show, Read, Eq)

eltScopeToTy :: EltScope -> EltTy
eltScopeToTy es = EltTy (_eltvarty . _eltinp $ es) (_eltty $ es)

data ScopedEltExp =
  ScopedEltExp { _eltscope :: EltScope , _eltExp :: EltExp }
  deriving (Show, Read, Eq)

data SpanExp
  = SpanEApp ModDeref EltExp EltExp
  deriving (Show, Read, Eq)

data SpanScope
  = SpanScope { _spancontra :: TypedEltVar, _spancovar :: TypedEltVar }
  deriving (Show, Read, Eq)

type ScopedSpanExp = (SpanScope, SpanExp)

data SpanTy
  = SpanTy { _spancontraty :: SetExp, _spancoty :: SetExp }
  deriving (Show, Read, Eq)

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
