module Semantics where

import Data.Bifunctor

import Util

-- | equivalent to NEListof Int, but more useful for operations
data DBRef
  = DBCurMod Int
  | DBOutMod DBRef
  deriving (Show, Eq)

substDBRef :: DBRef -> [ScopedVal] -> Either DBRef ScopedVal
substDBRef (DBCurMod n) g = Right $ g !! n
substDBRef (DBOutMod d) g = Left d

-- | 
data ScopedVal
  = SemSet SetNF
  | SemFun ScopedSemFun
  | SemSpan ScopedSemSpan
  | SemTrans ScopedSemTrans
-- | SemProof ??
  -- | SemSig -- TODO
  | SemMod ScopedSemMod  -- TODO

-- Push a value under a binder
shiftVal :: ScopedVal -> ScopedVal
shiftVal (SemSet db) = SemSet (shiftSet db)
shiftVal (SemFun (ScopedSemFun dom cod fun)) = SemFun (ScopedSemFun (shiftSet dom) (shiftSet cod) (shiftElt fun))
shiftVal (SemSpan (ScopedSemSpan contra covar span)) = SemSpan (ScopedSemSpan (shiftSet contra) (shiftSet covar) (shiftSpan span))
shiftVal (SemTrans (ScopedSemTrans ctx cod f)) = error "NYI: transsss" -- SemSpan (ScopedSemSpan (shiftSet contra) (shiftSet covar) (shiftSpan span))
shiftVal (SemMod (ScopedSemMod m)) = error "NYI" -- SemSpan (ScopedSemSpan (shiftSet contra) (shiftSet covar) (shiftSpan span))

subst :: ScopedVal -> [ScopedVal] -> ScopedVal
subst (SemSet s) g = SemSet (substSet s g)
subst (SemFun (ScopedSemFun dom cod f)) g = SemFun (ScopedSemFun (substSet dom g) (substSet cod g) (substElt f g))

shiftSet = DBOutMod

substSet :: SetNF -> [ScopedVal] -> SetNF
substSet s g = case substDBRef s g of
  Left r -> r
  Right (SemSet r) -> r

shiftElt ENFId = ENFId
shiftElt (ENFFunApp f t) = (ENFFunApp (DBOutMod f) (shiftElt t))

substElt :: EltNF -> [ScopedVal] -> EltNF
substElt ENFId g = ENFId
substElt (ENFFunApp f t) g = (\x -> unquoteSemFun x (substElt t g)) $ case (substDBRef f g) of
  Left r -> (ENFFunApp r ENFId)
  Right (SemFun (ScopedSemFun _ _ f)) -> f

shiftSpan (SNFSpanApp r contra covar) = SNFSpanApp (DBOutMod r) (shiftElt contra) (shiftElt covar)


data ScopedSemFun = ScopedSemFun { _scfunDom :: SetNF, _scfunCod :: SetNF, _scfun :: EltNF }

data ScopedSemSpan = ScopedSemSpan { _scspContra :: SetNF, _scspCovar :: SetNF, _scspan :: SpanNF }

type NamedSemTransCtx = ConsStar (String, SetNF, String, SpanNF) (String, SetNF)
type SemTransCtx = ConsStar (SetNF, SpanNF) SetNF

ctxIndices :: SemTransCtx -> NEList SetNF
ctxIndices = consStartoNE . first fst

ctxSpans :: SemTransCtx -> [SpanNF]
ctxSpans = allAs . first snd

ctxUnName :: NamedSemTransCtx -> SemTransCtx
ctxUnName = bimap (\(_,a,_,r) -> (a,r)) snd

boundary :: SemTransCtx -> (SetNF, SetNF)
boundary = firstAndLast . ctxIndices

data ScopedSemTrans
  = ScopedSemTrans { _sctransCtx  :: SemTransCtx
                   , _sctransCod     :: SpanNF   -- codomain
                   , _sctrans        ::([TransNF] -> TransNF) }

type SemTransSubst = [TransNF] -> [TransNF]

quoteSemFun :: (EltNF -> EltNF) -> EltNF
quoteSemFun f = f ENFId

unquoteSemFun :: EltNF -> (EltNF -> EltNF)
unquoteSemFun ENFId = id
unquoteSemFun (ENFFunApp f bod) = ENFFunApp f . unquoteSemFun bod

quoteSemSpan :: (EltNF -> EltNF -> SpanNF) -> SpanNF
quoteSemSpan r = r ENFId ENFId

unquoteSpan :: SpanNF -> (EltNF -> EltNF -> SpanNF)
unquoteSpan (SNFSpanApp r contra covar) contrain covarin = SNFSpanApp r (unquoteSemFun contra contrain) (unquoteSemFun covar covarin)

quoteSemTrans :: ([TransNF] -> TransNF) -> TransNF
quoteSemTrans t = t (repeat TNFId)

type SetNF = DBRef

data EltNF
  = ENFId
  | ENFFunApp DBRef EltNF
  deriving (Show, Eq)

data SpanNF = SNFSpanApp { _spanSymb :: DBRef, _contraElt :: EltNF, _covarElt :: EltNF }
  deriving (Show, Eq)

data TransNF
  = TNFId
  | TNFApp DBRef [TransNF]
  deriving (Show, Eq)

data ScopedSemMod = ScopedSemMod SemMod
type SemMod = [ScopedVal] -> [ScopedVal]
