{-# LANGUAGE TemplateHaskell #-}
module Semantics where

import Control.Lens
import Control.Monad.State
import Data.Bifunctor

import Util

-- | equivalent to NEListof Int, but more useful for operations
data DBRef
  = DBCurMod Int
  | DBOutMod DBRef
  deriving (Show, Eq)

type SetNF = DBRef

data EltNF
  = ENFId
  | ENFFunApp DBRef EltNF
  deriving (Show, Eq)

data ScopedFun = ScopedFun { _scfunDom :: SetNF, _scfunCod :: SetNF, _scfun :: EltNF }
$(makeLenses ''ScopedFun)

data SpanNF = SNFSpanApp { _spanSymb :: DBRef, _contraElt :: EltNF, _covarElt :: EltNF }
  deriving (Show, Eq)

data ScopedSpan = ScopedSpan { _scspContra :: SetNF, _scspCovar :: SetNF, _scspan :: SpanNF }
$(makeLenses ''ScopedSpan)

data TransNF
  = TNFId
  | TNFApp DBRef [TransNF]
  deriving (Show, Eq)

type NamedTransCtx = ConsStar (String, SetNF, String, SpanNF) (String, SetNF)
type TransCtx = ConsStar (SetNF, SpanNF) SetNF

data ScopedTrans
  = ScopedTrans { _sctransCtx  :: TransCtx -- domains
                   , _sctransCod  :: SpanNF      -- codomain
                   , _sctrans     :: TransNF }
$(makeLenses ''ScopedTrans)

-- | 
data ScopedVal
  = ScSet SetNF
  | ScFun ScopedFun
  | ScSpan ScopedSpan
  | ScTrans ScopedTrans
-- | SemProof ??
  -- | SemSig -- TODO
  | ScMod ScopedMod  -- TODO

data Type
  = TypeSet
  | TypeFun SetNF SetNF
  | TypeSpan SetNF SetNF
  | TypeTrans TransCtx SpanNF

substDBRef :: DBRef -> [ScopedVal] -> Either DBRef ScopedVal
substDBRef (DBCurMod n) g = Right $ g !! n
substDBRef (DBOutMod d) g = Left d

typeOf :: ScopedVal -> Type
typeOf (ScSet _) = TypeSet
typeOf (ScFun (ScopedFun dom cod _)) = TypeFun dom cod
typeOf (ScSpan (ScopedSpan contra covar _)) = TypeSpan contra covar
typeOf (ScTrans (ScopedTrans ctx cod _)) = TypeTrans ctx cod
typeOf (ScMod _) = error "NYI: first class modules"

dbVal :: DBRef -> Type -> ScopedVal
dbVal n (TypeSet) = ScSet n
dbVal n (TypeFun dom cod) = ScFun $ ScopedFun dom cod (ENFFunApp n ENFId)
dbVal n (TypeSpan contra covar) = ScSpan $ ScopedSpan contra covar (SNFSpanApp n ENFId ENFId)
dbVal n (TypeTrans doms cod) = ScTrans $ ScopedTrans doms cod (TNFApp n (map (const TNFId) . ctxSpans $ doms))


-- Push a value under a binder
shiftVal :: ScopedVal -> ScopedVal
shiftVal (ScSet db) = ScSet (shiftSet db)
shiftVal (ScFun (ScopedFun dom cod fun)) = ScFun (ScopedFun (shiftSet dom) (shiftSet cod) (shiftElt fun))
shiftVal (ScSpan (ScopedSpan contra covar span)) = ScSpan (ScopedSpan (shiftSet contra) (shiftSet covar) (shiftSpan span))
shiftVal (ScTrans (ScopedTrans ctx cod f)) = error "NYI: transsss" -- Span (ScopedSpan (shiftSet contra) (shiftSet covar) (shiftSpan span))
shiftVal (ScMod (ScopedMod sc m)) = error "NYI" -- Span (ScopedSpan (shiftSet contra) (shiftSet covar) (shiftSpan span))

subst :: ScopedVal -> [ScopedVal] -> ScopedVal
subst (ScSet s) g = ScSet (substSet s g)
subst (ScFun (ScopedFun dom cod f)) g = ScFun (ScopedFun (substSet dom g) (substSet cod g) (substElt f g))
subst _ _ = error "NYI: substitution for spans, transformations, modules, signatures"

shiftSet = DBOutMod

substSet :: SetNF -> [ScopedVal] -> SetNF
substSet s g = case substDBRef s g of
  Left r -> r
  Right (ScSet r) -> r

shiftElt ENFId = ENFId
shiftElt (ENFFunApp f t) = (ENFFunApp (DBOutMod f) (shiftElt t))

substElt :: EltNF -> [ScopedVal] -> EltNF
substElt ENFId g = ENFId
substElt (ENFFunApp f t) g = (\x -> unquoteFun x (substElt t g)) $ case (substDBRef f g) of
  Left r -> (ENFFunApp r ENFId)
  Right (ScFun (ScopedFun _ _ f)) -> f

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

data ScopedMod = ScopedMod ModScope ModNF
type ModScope = ()

data ModNF
  = ModNFApp  DBRef [ScopedVal]
  | ModNFBase [Type] [(String, ScopedVal)]

