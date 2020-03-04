{-# LANGUAGE TemplateHaskell #-}
module Semantics where

import Control.Lens
import Control.Monad.State
import Data.Bifunctor

import Util

-- | equivalent to NEListof Int, but more useful for operations
data DBRef
  = DBCurMod Int -- direct reference to something in the current module
  | DBOutMod DBRef --reference to something in the outer module
  deriving (Show, Eq)

data Lookup
  = LookRef DBRef -- reference to the val
  | LookSel ModNeu String -- select from an as-yet undetermined module
  deriving (Show, Eq)
type SetNF = Lookup

data EltNF
  = ENFId
  | ENFFunApp Lookup EltNF
  deriving (Show, Eq)

data FunTy = FunTy { _funDom :: SetNF, _funCod :: SetNF }
  deriving (Show, Eq)

data ScopedFun = ScopedFun { _scfunTy :: FunTy, _scfun :: EltNF }
  deriving (Show, Eq)

data SpanNF = SNFSpanApp { _spanSymb :: Lookup, _contraElt :: EltNF, _covarElt :: EltNF }
  deriving (Show, Eq)

data ScopedSpan = ScopedSpan { _scspContra :: SetNF, _scspCovar :: SetNF, _scspan :: SpanNF }
  deriving (Show, Eq)

data TransNF
  = TNFId
  | TNFApp Lookup [TransNF]
  deriving (Show, Eq)

type NamedTransCtx = ConsStar (String, SetNF, String, SpanNF) (String, SetNF)
type TransCtx = ConsStar (SetNF, SpanNF) SetNF

data ScopedTrans
  = ScopedTrans { _sctransCtx  :: TransCtx -- domains
                   , _sctransCod  :: SpanNF      -- codomain
                   , _sctrans     :: TransNF }
  deriving (Show, Eq)
data ScopedMod = ScopedMod { _modScop :: ModScope, _modNF :: ModNF }
  deriving (Show, Eq)
type ModScope =  [Type]

data ModNF
  = ModNFNeu  ModNeu
  | ModNFBase [(String, ScopedVal)]
  deriving (Show, Eq)
type SigScope = [Type]
type SigNF = [(String, Type)]
data ScopedSig = ScopedSig { _scsigScope :: SigScope, _scsig :: SigNF }
  deriving (Show, Eq)
data ModNeu
  = MNeuRef DBRef -- direct reference
  | MNeuApp ModNeu ScopedVal -- application of a module to a value
  | MNeuSel ModNeu String -- selection of a field from a module
  deriving (Show, Eq)
-- | 
data ScopedVal
  = ScSet SetNF
  | ScFun ScopedFun
  | ScSpan ScopedSpan
  | ScTrans ScopedTrans
-- | SemProof ?? -- TODO
  | ScMod ScopedMod
  | ScSig ScopedSig
  deriving (Show, Eq)

data Type
  = TypeSet
  | TypeFun FunTy
  | TypeSpan SetNF SetNF
  | TypeTrans TransCtx SpanNF
  -- | TypeAxiom
  | TypeMod ScopedSig
  deriving (Show, Eq)
$(makeLenses ''FunTy)
$(makeLenses ''ScopedFun)
$(makeLenses ''ScopedSpan)
$(makeLenses ''ScopedTrans)
$(makeLenses ''ScopedSig)
$(makeLenses ''ScopedMod)


substDBRef :: DBRef -> [ScopedVal] -> Either DBRef ScopedVal
substDBRef (DBCurMod n) g = Right $ g !! n
substDBRef (DBOutMod d) g = Left d

substLookup :: Lookup -> [ScopedVal] -> Either Lookup ScopedVal
substLookup (LookRef db)    g = first LookRef . substDBRef db $ g
substLookup (LookSel neu s) g = case substModNeu neu g of
  ModNFNeu neu -> Left $ LookSel neu s
  ModNFBase ds -> Right $ select ds s

select :: [(String, ScopedVal)] -> String -> ScopedVal
select ds s = case lookup s ds of
  Just v -> v

substModNeu :: ModNeu -> [ScopedVal] -> ModNF
substModNeu (MNeuRef db) g = case substDBRef db g of
  Left db -> ModNFNeu (MNeuRef db)
  Right (ScMod m) -> m ^. modNF
substModNeu (MNeuSel neu s) g = case substModNeu neu g of
  ModNFNeu neu -> ModNFNeu (MNeuSel neu s)
  ModNFBase ds -> case select ds s of
    ScMod m -> m ^. modNF
substModNeu (MNeuApp neu v) g = error "NYI: first class parameterized modules"


-- select :: 

-- select :: [String] -> 

typeOf :: ScopedVal -> Type
typeOf (ScSet _) = TypeSet
typeOf (ScFun (ScopedFun sc _)) = TypeFun sc
typeOf (ScSpan (ScopedSpan contra covar _)) = TypeSpan contra covar
typeOf (ScTrans (ScopedTrans ctx cod _)) = TypeTrans ctx cod
typeOf (ScMod _) = error "NYI: first class modules"

-- eta expand a dbreference to make it a NF
dbVal :: DBRef -> Type -> ScopedVal
dbVal = error "TODO"

-- dbVal n (TypeSet) = ScSet n
-- dbVal n (TypeFun tau) = ScFun $ ScopedFun tau (ENFFunApp n ENFId)
-- dbVal n (TypeSpan contra covar) = ScSpan $ ScopedSpan contra covar (SNFSpanApp n ENFId ENFId)
-- dbVal n (TypeTrans doms cod) = ScTrans $ ScopedTrans doms cod (TNFApp n (map (const TNFId) . ctxSpans $ doms))
-- dbVal n (TypeMod sig) = ScMod $ ScopedMod (sig ^. scsigScope) (ModNFBase $ sig ^. scsig & traversed %@~ mkDeref)
--   where mkDeref :: Int -> (String, Type) -> (String, ScopedVal)
--         mkDeref = _

-- Push a value under a binder
shiftVal :: ScopedVal -> ScopedVal
shiftVal (ScSet s) = ScSet (shiftSet s)
shiftVal (ScFun (ScopedFun ty fun)) = ScFun (ScopedFun (shiftFunTy ty) (shiftElt fun))
shiftVal (ScSpan (ScopedSpan contra covar span)) = ScSpan (ScopedSpan (shiftSet contra) (shiftSet covar) (shiftSpan span))
shiftVal (ScTrans (ScopedTrans ctx cod f)) = error "NYI: shifting transsss" -- Span (ScopedSpan (shiftSet contra) (shiftSet covar) (shiftSpan span))
shiftVal (ScMod (ScopedMod sc m)) = error "NYI: shifting mods" -- Span (ScopedSpan (shiftSet contra) (shiftSet covar) (shiftSpan span))
shiftVal (ScSig (ScopedSig ps bod)) = ScSig $ ScopedSig (ps & traverse %~ shiftType) (bod & traverse . _2 %~ shiftType)

shiftType :: Type -> Type
shiftType TypeSet = TypeSet
shiftType (TypeFun t) = TypeFun $ shiftFunTy t

subst :: [ScopedVal] -> ScopedVal -> ScopedVal
subst g (ScSet s) = ScSet (substSet g s)
subst g (ScFun (ScopedFun t f)) = ScFun (ScopedFun (substFunTy g t) (substElt g f))
subst _ _ = error "NYI: substitution for spans, transformations, modules, signatures"

shiftLookup :: Lookup -> Lookup
shiftLookup (LookRef db) = LookRef (DBOutMod db)
shiftLookup (LookSel neu s) = LookSel (shiftNeu neu) s

shiftNeu :: ModNeu -> ModNeu
shiftNeu = error "TODO"

shiftSet :: SetNF -> SetNF
shiftSet = shiftLookup

substSet :: [ScopedVal] -> SetNF -> SetNF
substSet g s = case substLookup s g of
  Left r -> r
  Right (ScSet r) -> r

shiftFunTy :: FunTy -> FunTy
shiftFunTy t = t & funDom %~ shiftSet & funCod %~ shiftSet

shiftElt ENFId = ENFId
shiftElt (ENFFunApp f t) = (ENFFunApp (DBOutMod f) (shiftElt t))

substFunTy :: [ScopedVal] -> FunTy -> FunTy
substFunTy g t = t & funDom %~ substSet g & funCod %~ substSet g
  
substElt :: [ScopedVal] -> EltNF -> EltNF
substElt g ENFId = ENFId
substElt g (ENFFunApp f t) = (\x -> unquoteFun x (substElt g t)) $ case (substDBRef f g) of
  Left r -> (ENFFunApp r ENFId)
  Right (ScFun (ScopedFun _ f)) -> f

shiftSpan (SNFSpanApp r contra covar) = SNFSpanApp (DBOutMod r) (shiftElt contra) (shiftElt covar)

namedIndices :: NamedTransCtx -> NEList (String, SetNF)
namedIndices = consStartoNE . first (\(x,s,_,_) -> (x,s))

ctxIndices :: TransCtx -> NEList SetNF
ctxIndices = consStartoNE . first fst

ctxScopeSpans :: TransCtx -> [ScopedSpan]
ctxScopeSpans = snd . foldConsStar cons done
  where cons (contra, span) (covar, spans) = (contra, ScopedSpan contra covar span :spans)
        done covar = (covar, [])

ctxSpans :: TransCtx -> [SpanNF]
ctxSpans = allAs . first snd

ctxUnName :: NamedTransCtx -> TransCtx
ctxUnName = bimap (\(_,a,_,r) -> (a,r)) snd

boundary :: TransCtx -> (SetNF, SetNF)
boundary = firstAndLast . ctxIndices

quoteFun :: (EltNF -> EltNF) -> EltNF
quoteFun f = f ENFId

unquoteFun :: EltNF -> (EltNF -> EltNF)
unquoteFun ENFId = id
unquoteFun (ENFFunApp f bod) = ENFFunApp f . unquoteFun bod

quoteSpan :: (EltNF -> EltNF -> SpanNF) -> SpanNF
quoteSpan r = r ENFId ENFId

unquoteSpan :: SpanNF -> (EltNF -> EltNF -> SpanNF)
unquoteSpan (SNFSpanApp r contra covar) contrain covarin = SNFSpanApp r (unquoteFun contra contrain) (unquoteFun covar covarin)

quoteTrans :: ([TransNF] -> TransNF) -> TransNF
quoteTrans t = t (repeat TNFId)

unquoteTrans :: TransNF -> ([TransNF] -> TransNF)
unquoteTrans = evalState . unquoteTransComp

pop :: State [a] a
pop = do
  x:xs <- get
  put xs
  return x

unquoteTransComp :: TransNF -> State [TransNF] TransNF
unquoteTransComp TNFId         = pop
unquoteTransComp (TNFApp f ts) = TNFApp f <$> unquoteTransSubstComp ts

unquoteTransSubst :: [TransNF] -> ([TransNF] -> [TransNF])
unquoteTransSubst = evalState . unquoteTransSubstComp

unquoteTransSubstComp :: [TransNF] -> State [TransNF] [TransNF]
unquoteTransSubstComp = traverse unquoteTransComp

