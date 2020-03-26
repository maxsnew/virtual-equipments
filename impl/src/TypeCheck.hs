{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
module TypeCheck where

import Control.Applicative
import Control.Lens
import Data.Functor
import Data.String
import qualified Data.List as List
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import Data.Foldable
import Data.Traversable

import Syntax
import Semantics
import Util


data Decl name a = Decl { _name :: name , _defn :: a }
  deriving (Show, Read, Eq, Functor)

$(makeLenses ''Decl)

type SynDecl = Decl String

lookupDecl :: (Eq name) => name -> [Decl name a] -> Maybe a
lookupDecl s xs = lookup s (map declToPair xs)
  where
    declToPair :: Decl name a -> (name, a)
    declToPair d = (_name d, _defn d)

data Ctx
  = CtxTopLvl { _localBindings :: [SynDecl ScopedVal], _numParams :: Int }
  | CtxSubMod { _localBindings :: [SynDecl ScopedVal], _numParams :: Int, _restCtx :: Ctx }

$(makeLenses ''Ctx)

-- | Typechecking here is combined with parsing the sexpression,
-- unfortunately. The effects are as follows:
-- 1. We can throw type/parse errors
-- 2. We accumulate bindings in the Ctx
-- 3. We consume the s-expression as we go

-- There are two monads involved
-- One for parsing a sequence of S-expressions
newtype TCS a = TCS { runTCS :: StateT ([ParsedSExp], Ctx) (ExceptT ErrMsg Identity) a }
  deriving (Functor,Applicative,Monad,Alternative,MonadError ErrMsg, MonadState ([ParsedSExp], Ctx))

-- And one for parsing a single S-expression
newtype TC a = TC { runTC :: ReaderT ParsedSExp (StateT Ctx (ExceptT ErrMsg Identity)) a }
  deriving (Functor,Applicative,Monad,Alternative,MonadError ErrMsg, MonadReader ParsedSExp, MonadState Ctx)

newtype ErrMsg = ErrMsg { _getMsg :: Last String }
  deriving (Show, Read, Eq, Monoid)

instance IsString ErrMsg where
  fromString = ErrMsg . Last . Just

mtCtx :: Ctx
mtCtx = CtxTopLvl [] 0
  
ctx :: TCS Ctx
ctx = snd <$> get

typeCheck :: TCS a -> [ParsedSExp] -> Either String a
typeCheck (TCS m) exps =
  lErrToStr .  fmap fst $ runIdentity $ runExceptT $ runStateT m (exps, mtCtx)
  

typeCheckOne :: TC a -> ParsedSExp -> Either String a
typeCheckOne p exp = typeCheck (single p) [exp]

lErrToStr = either (Left . errToStr) Right

errToStr :: ErrMsg -> String
errToStr (ErrMsg (Last Nothing)) = "internal error: no cases"
errToStr (ErrMsg (Last (Just s))) = s

localize :: (MonadState s m) => m a -> m a
localize m = do
  s <- get
  x <- m
  put s
  return x

enter :: TC a -> TC a
enter m = do
  modify $ CtxSubMod [] 0
  x <- m
  modify ctxTl
  return x
  where
    ctxTl (CtxSubMod _ _ tl) = tl

-- | typecheck the head of the current seq
tcHd :: TC a -> TCS a
tcHd p = TCS . StateT $ \(sexps, ctx) ->
  case sexps of
    [] -> empty
    (x:xs) -> do
      (a, ctx) <- runStateT (runReaderT (runTC p) $ x) ctx
      return (a, (xs,ctx))

mayHd :: TC a -> TCS (Maybe a)
mayHd p = Just <$> tcHd p <|> return Nothing

-- ensure there's nothing left
done :: TCS ()
done = fst <$> get >>= \case
  [] -> return ()
  _  -> throwError $ "there's some junk here"

single :: TC a -> TCS a
single p = tcHd p <* done

-- "hanndle" the reader effect using the state effect?
list :: TCS a -> TC a
list k = TC . ReaderT $ \sexp -> StateT $ \ctx -> case _sexp sexp of
  SEAtom a -> throwError $ "expected a list, but got an atom"
  SEList sexps -> do
    (x, (leftover, ctx)) <- runStateT (runTCS k) (sexps, ctx)
    guard $ null leftover
    return (x, ctx)

unlist :: TC a -> TCS a
unlist p = TCS . StateT $ \(exps, ctx) ->
  fmap ((,) exps) <$>
  runStateT (runReaderT (runTC p) (ParsedSExp (error "internal error: don't look at me") (SEList exps))) ctx

several :: TC a -> TCS [a]
several tc = ([] <$ done) <|> ((:) <$> tcHd tc <*> several tc)

atLeastOne :: TC a -> TCS (NEList a)
atLeastOne p = ((Done <$> tcHd p) <* done) <|> (Cons <$> tcHd p <*> atLeastOne p)

anyAtom :: TC String
anyAtom = _sexp <$> ask >>= \case
  SEAtom x -> return x
  SEList _ -> throwError $ "got a list, wanted an atom"

atomEq  :: String -> TC ()
atomEq s = do
  at <- anyAtom
  guard $ at == s

program :: TCS [SynDecl ScopedVal]
program = moduleBody

moduleBody :: TCS [SynDecl ScopedVal]
moduleBody = several decl

declare :: SynDecl ScopedVal -> TCS ()
declare d = (_2 . localBindings) %= (d:)

sideeffect :: Monad m => (a -> m ()) -> m a -> m a
sideeffect k m = do
  x <- m
  k x
  return x


-- Unification

-- given two spans R[a;b] and R'[a';b']
-- find most general A,B,A',B'
-- such that
-- R[A;B] = R'[A';B']
unifySpans :: (IsString e, MonadError e m) => SpanNF -> SpanNF -> m ((EltNF, EltNF), (EltNF, EltNF))
SNFSpanApp r1 f1 g1 `unifySpans` SNFSpanApp r2 f2 g2 =
  if r1 /= r2
  then throwError "transformation type error"
  else (,) <$> (f1 `unifyFuns` f2) <*> (g1 `unifyFuns` g2)

unifyFuns :: (IsString e, MonadError e m) => EltNF -> EltNF -> m (EltNF, EltNF)
ENFId `unifyFuns` f2 = return (f2, ENFId)
f1 `unifyFuns` ENFId = return (ENFId, f1)
ENFFunApp f1 e1 `unifyFuns` ENFFunApp f2 e2 =
  if f1 /= f2 then throwError "transformation type error"
  else e1 `unifyFuns` e2

-- special directed case of unification.  want to find an
-- instantiation of the second arg that makes it equal to the first.
spanDecomposesInto :: (IsString e, MonadError e m) => SpanNF -> SpanNF -> m (EltNF, EltNF)
s1 `spanDecomposesInto` s2 = do
  (shouldBeIds, res) <- s1 `unifySpans` s2
  when (shouldBeIds /= (ENFId, ENFId)) $ throwError "something was not an instantiation of something else"
  return res

-- f `fdi` g ~> h then f = quote (unquote g h)
funDecomposesInto :: (IsString e, MonadError e m) => EltNF -> EltNF -> m EltNF
e1 `funDecomposesInto` e2 = do
  (shouldBeId, res) <- e1 `unifyFuns` e2
  when (shouldBeId /= ENFId) $ throwError "something was not an inst of something elsee"
  return res
  
decl :: TC (SynDecl ScopedVal)
decl = list $
  tcSemDecl "def-mod" (ScMod <$> single modul)
  <|> tcSemDecl "def-sig" (ScSig <$> single sig)
  <|> tcSemDecl "def-set"   (ScSet   <$> single setVal)
  <|> tcSemDecl "def-fun"   (ScFun   <$> scopedFunVal)
  <|> tcSemDecl "def-span"  (ScSpan  <$> scopedSpanVal)
  <|> tcSemDecl "def-trans" (ScTrans <$> scopedTransVal)
  -- (def-trans t (a b c d) (Rab Sbc Qcd) Tad bod)
  -- TODO: assertion, signature
  where
    tcDecl :: String -> TCS a -> TCS (SynDecl a)
    tcDecl def p = tcHd (atomEq def) *> (Decl <$> tcHd anyAtom <*> p)
    
    tcSemDecl :: String -> TCS ScopedVal -> TCS (SynDecl ScopedVal)
    tcSemDecl def p = sideeffect declare $ tcDecl def p

-- (sig () param ...) -- sig value
-- (sig (param param ...) param ...) -- sig lambda
-- or S
-- or (S ...)
-- or (. C ...)
-- sigExp :: TC SigExp
-- sigExp = list $ tcHd (atomEq "sig") >> return dummy
--   where dummy = SigBase . GSigVar $ "NYI"
  -- parse, don't check sigBase <|> sigApp
  -- where
  --   sigBase = SigBase <$> (GSigVar <$> sigVar <|> GSigVal <$> sigVal <|> GSigLam <$> sigLam)
  --   sigVar  = do
  --     var <- anyAtom
  --     ctx <- get
  --     case fmap isSig $ lookupSynDecl var ctx of
  --       Just True -> return var
  --       _ -> empty
  --   sigLam = localize . list $ tcHd (atomEq "psig") >> SigLam <$> tcHd (list params) <*> params
  --   sigVal = localize . list $ tcHd (atomEq "sig") >> params

  --   sigApp :: TC SigExp
  --   sigApp = empty -- TODO: signature application

-- (mod (param ...) sig param ...)
-- or C
-- or (. C ...)
-- or (M anyExpr ...) TODO
modul :: TC ScopedMod
modul = modulVar
      <|> modulLam
  where
    modulVar = modDeref >>= \case
      ScMod m -> return m
      _ -> empty

    modulLam = enter . list $
      tcHd (atomEq "mod") *> do
      ps <- tcHd (list (several param))
      sig <- mayHd empty
      modBod <- moduleBody
      return $ ScopedMod ps (ModNFBase (map undecl modBod))

    undecl (Decl a b) = (a,b)

-- (sig (param ...) (param ...))
-- modDeref
-- (S val ...) ??
sig :: TC ScopedSig
sig = sigVar <|> sigLam
  where
    sigVar = modDeref >>= \case
      ScSig s -> return s
      _ -> empty

    sigLam = enter . list $
      tcHd (atomEq "sig") *> do
      ScopedSig <$> tcHd (list (several param)) <*> several namedParam
      

setVal :: TC SetNF
setVal = modDeref >>= \case
  ScSet n -> return n
  _ -> throwError $ "expected a set, but got...something else"

-- (x A) B t
scopedFunVal :: TCS ScopedFun
scopedFunVal = do
  (x, dom) <- tcHd eltVar
  cod <- tcHd setVal
  t <- single $ elt x dom cod
  return $ ScopedFun (FunTy dom cod) t

eltVar :: TC (String, SetNF)
eltVar = list $ (,) <$> tcHd anyAtom <*> single setVal

elt :: String -> SetNF -> SetNF -> TC EltNF
elt x dom cod =
  (atomEq x *> guard (dom == cod) *> return ENFId)
  <|> (list $ do
  f <- tcHd funVar
  guard $ cod == (f ^. (scfunTy . funCod))
  arg <- single $ elt x dom (f ^. (scfunTy . funDom))
  return $ unquoteFun (f ^. scfun) arg)
  where
    funVar = modDeref >>= \case
      ScFun f -> return f
      _ -> throwError $ "expected a function but gott...something else"

-- (x A) (y B) t
scopedSpanVal :: TCS ScopedSpan
scopedSpanVal = do
  (contraX, contraSet) <- tcHd eltVar
  (covarX,   covarSet) <- tcHd eltVar
  s <- single $ spanVal contraX contraSet covarX covarSet
  return $ ScopedSpan contraSet covarSet s

spanVal :: String -> SetNF -> String -> SetNF -> TC SpanNF
spanVal contraX contraSet covarX covarSet =
  list $ do
  r <- tcHd spanVar
  contraArg <- tcHd $ elt contraX contraSet (r ^. scspContra)
  covarArg  <- tcHd $ elt covarX  covarSet  (r ^. scspCovar)
  return $ unquoteSpan (r ^. scspan) contraArg covarArg
  where spanVar = modDeref >>= \case
          ScSpan r -> return r
          _ -> throwError "expected a span but got something else"

-- ((a X) (b Y) (c Z)) ((r (R a b)) (q (Q b c))) (P a c) bod
scopedTransVal :: TCS ScopedTrans
scopedTransVal = do
  indices <- tcHd $ spanStringIndices
  ctx     <- tcHd . list $ transCtx indices
  let ((contraX, contraSet), (covarX, covarSet)) = firstAndLast $ indices
  cod     <- tcHd $ spanVal contraX contraSet covarX covarSet
  single $ (ScopedTrans (ctxUnName ctx) cod <$> transValChk ctx cod)

transCtx :: NEList (String, SetNF) -> TCS NamedTransCtx
transCtx (Done x)    = done $> DoneB x
transCtx (Cons (contraX, contraSet) indices) =
  let (covarX, covarSet) = indices ^. neHd in do
  (spanX, span) <- tcHd $ spanVarChk contraX contraSet covarX covarSet
  ConsA (contraX, contraSet, spanX, span) <$> transCtx indices

spanVarChk :: String -> SetNF -> String -> SetNF -> TC (String, SpanNF)
spanVarChk contraX contraSet covarX covarSet =
  list $ (,) <$> tcHd anyAtom <*> single (spanVal contraX contraSet covarX covarSet)

transValChk :: NamedTransCtx -> SpanNF -> TC TransNF
transValChk doms cod = transValChkComp doms cod >>= \case
  (DoneB _, _, t) -> return t
  (ConsA _ _, _, _) -> throwError "unused variables in transformation"

-- we are given Phi, R
-- we parse a t and produce a Phi_r and the (unique?, most general?) B such that
-- Phi = Phi_l,Phi_r
-- Phi_l |- t : R[Id;B]
transValChkComp :: NamedTransCtx -> SpanNF -> TC (NamedTransCtx, EltNF, TransNF)
transValChkComp doms cod = idVal <|> list appVal
  where
    idVal = do
      x <- anyAtom
      case doms of
        ConsA (_, _, y, ySpan) leftovers -> do
          when (x /= y) $ throwError "used the wrong transformation variable"
          ((contraCodF,covarCodF), (contraDomF,covarDomF)) <- cod `unifySpans` ySpan
          when (contraDomF /= ENFId || covarDomF /= ENFId) $ throwError "variable's type is too general"
          when (contraCodF /= ENFId) $ throwError "transformation type error"
          return (leftovers, covarCodF, TNFId)
        (DoneB _) -> throwError "unbound transformation variable"
    -- (f t1 t2 t3)
    appVal :: TCS (NamedTransCtx, EltNF, TransNF)
    appVal = tcHd modDeref >>= \case

      -- want to find Phi_l, B
      -- Phi_l |- f(t,...) : R[id;B]
      -- we get f : forall ixs... Phi_f => S
      -- we then need to see that R[id;-] is an instantiation S
      -- then check that
      -- Phi_l |- t,... : Phi_f[A';-]
      ScTrans f -> do
        -- we have R_exp[A;B] = R_f[A';B']
        ((contraCodF,covarCodF), (contrafF, covarfF)) <- cod `unifySpans` (f ^. sctransCod)
        when (contraCodF /= ENFId) $ throwError "transformation type error of some sort"
        (leftovers, covarResultF, args) <- transSubstChkComp doms contrafF (f ^. sctransCtx)
        return (leftovers, unquoteFun covarCodF covarResultF, unquoteTrans (f ^. sctrans) args)
        -- unquoteSemTrans (f ^. sctrans) <$> transSubstChk (f ^. sctransCtx)
      _ -> throwError "expected a transformation but got...something else"

transSubstChkComp :: NamedTransCtx -> EltNF -> TransCtx -> TCS (NamedTransCtx, EltNF, [TransNF])
transSubstChkComp doms contraFun cods = case cods of
  DoneB _   -> done $> (doms, contraFun, [])
  ConsA (_, codSpan) cods -> do
    (leftovers, covarFun , arg) <- tcHd $ transValChkComp doms (unquoteSpan codSpan contraFun ENFId)
    (_3 %~ (arg:)) <$> transSubstChkComp leftovers covarFun cods

spanStringIndices :: TC (NEList (String, SetNF))
spanStringIndices = list (atLeastOne eltVar)

spanString :: NEList (String, SetNF) -> TCS TransCtx
spanString (Done x) = done $> DoneB (snd x)
spanString (Cons (contraVar, contraSet) xs) =
  let (covarVar, covarSet) = xs ^. neHd in do
  spn <- tcHd $ spanVal contraVar contraSet covarVar covarSet
  ConsA (contraSet, spn) <$> spanString xs

modDeref :: TC ScopedVal
modDeref =
  join (resolveBinding <$> anyAtom <*> get)
  <|> list (tcHd (atomEq ".") *> join (select <$> tcHd modul <*> atLeastOne anyAtom))
  where
    resolveBinding :: String -> Ctx -> TC ScopedVal
    resolveBinding s c = case c ^. localBindings of
      []   -> case c ^? restCtx of
        Nothing -> throwError $ "unbound variable"
        Just rest -> shiftVal <$> resolveBinding s rest
      b:bs ->
        if _name b == s
        then return $ _defn b
        else resolveBinding s (c & localBindings .~ bs)

    select :: ScopedMod -> NEList String -> TCS ScopedVal
    select (ScopedMod sc mod) (Done s)    = selectOne sc mod s
    select (ScopedMod sc mod) (Cons s ss) = selectOne sc mod s >>= \case
      ScMod m -> select m ss

    selectOne :: ModScope -> ModNF -> String -> TCS ScopedVal
    selectOne (_:_) _ s = throwError "Tried to select from a parameterized module that is not fully applied"
    selectOne [] (ModNFNeu neu) s = selectOneNeu neu s
    selectOne [] (ModNFBase ds) s = case lookup s ds of
      Nothing -> error "Tried to select a value not in the module"
      Just x  -> return x

    selectOneNeu :: ModNeu -> String -> TCS ScopedVal
    selectOneNeu n s = case n of
      MNeuRef db sig -> case lookup s sig of
        Nothing -> throwError "Tried to select a field from a module that doesn't support it"
        Just ty -> return $ etaLookup (LookSel n s) ty
      MNeuSel neu s'  -> throwError "Haven't yet implemented multiple selection"
      MNeuApp neu val -> throwError "First class parameterized modules aren't yet supported"

-- | check the generator for validity and then add the declaration to
-- the context

nextDB :: TCS DBRef
nextDB = DBCurMod <$> (_2 . numParams <<+= 1)

denoteGenerator :: Type -> TCS ScopedVal
denoteGenerator ty = flip dbVal ty <$> nextDB

declareGenerator :: SynDecl Type -> TCS ()
declareGenerator declGen = declare =<< defn denoteGenerator declGen
    
-- | Has the effect of extending the current context
param :: TC Type
param = snd <$> namedParam

namedParam :: TC (String, Type)
namedParam = list $
  (genName "set" (done $> TypeSet))
  <|> genName "fun"   (TypeFun  <$> (FunTy <$> tcHd setVal <*> tcHd setVal) <* done)
  <|> genName "span"  (TypeSpan <$> tcHd setVal <*> tcHd setVal <* done)
  -- (trans t ((a X) (b Y) (c Z) (d W)) ((R a b) (S b c) (Q d c)) (P a d))
  <|> genName "trans" (do
      indices <- tcHd spanStringIndices
      ctx <- tcHd . list $ spanString indices
      let ((contraX, contraSet), (covarX, covarSet)) = firstAndLast $ indices
      cod <- single (spanVal contraX contraSet covarX covarSet)
      return $ TypeTrans ctx cod)
  <|> (genName "mod" $ single (TypeMod <$> sig))
  where
    genName :: String -> TCS Type -> TCS (String, Type)
    genName key p = do
      d <- ((tcHd (atomEq key)) *> (Decl <$> tcHd anyAtom <*> p))
      declareGenerator d
      return (d ^. name, d ^. defn)

