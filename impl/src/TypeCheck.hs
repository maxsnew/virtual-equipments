{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
module TypeCheck where

import Control.Applicative
import Control.Lens
import Data.Functor
import Data.String
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

data Ctx
  = CtxTopLvl { _localBindings :: [SynDecl ScopedVal], _numParams :: Int }
  | CtxSubMod { _localBindings :: [SynDecl ScopedVal], _numParams :: Int, _restCtx :: Ctx }

$(makeLenses ''Ctx)

-- | Typechecking here is combined with parsing the sexpression,
-- unfortunately. The effects are as follows:
-- 1. We can throw type/parse errors
-- 2. We accumulate bindings in the Ctx
-- 3. We consume the s-expression as we go

-- The basic process is that we take in an S-expression, produce an
-- AST for the purposes of parsing but in the context we produce
-- semantic values for the purposes of simple equality checking

-- TODO: there should really be a separation of parse errors/parse
-- state and tc errors/tc state here. Right now we're getting them mixed up and it's annoying

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

-- throwLocErr :: (Monaderror m ErrMsg) => String -> m a
-- throwLocErr expected = do
--   p <- fst <$> get
--   throwError $ "Error at " ++ show (_loc p) ++ " expected a " ++ expected  ++  ", but got: " ++ show (_sexp p)


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

-- denoteSpanString :: NEList (String, SetNF) -> [SpanVar] -> TCS NamedSemTransCtx
-- denoteSpanString (Done tvar) [] = return $ DoneB tvar
-- denoteSpanString (Cons (contravar, contraset) vars) ((SpanVar spanVar spanE) : es) = do
--   span <- denoteSpan contravar contraset covarvar covarset spanE
--   ConsA (contravar, contraset, spanVar, span) <$> denoteSpanString vars es
--   where (covarvar, covarset) = neHd vars
-- denoteSpanString (Done _) (e : es) = throwError $ "not enough indices for the inputs of a transformation"
-- denoteSpanString (Cons _ _) [] = throwError $ "too many indices for the inputs of a transformation"

-- denoteScopedTrans :: ScopedTransExp -> TCS ScopedSemTrans
-- denoteScopedTrans (ScopedTransExp (TransScope indicesE varsE codE) e) = do
--   indices <- traverse (\tvar -> (,) (_eltvar tvar) <$> denoteSet (_eltvarty tvar)) indicesE
--   ctx <- denoteSpanString indices varsE
--   let ((contravar, contraty), (covarvar, covarty)) = firstAndLast indices
--   cod <- denoteSpan contravar contraty covarvar covarty codE
--   f <- denoteTrans ctx cod e
--   return $ ScopedSemTrans (ctxUnName ctx) cod f

-- -- this will probably have to change to do some inference when we add
-- -- positive types (hom/tensor), though probably not when we add
-- -- negative types like cotensor/products/pullbacks
-- denoteTrans :: NamedSemTransCtx -> SpanNF -> TransExp -> TCS ([TransNF] -> TransNF)
-- denoteTrans ctx codSpan (TransEVar x) = case ctx of
--   ConsA (alphaContra, contraSet, spanVar, domSpan) (DoneB (betaCovar, covarSet)) ->
--     if x == spanVar && codSpan == domSpan
--     then return $ \[t] -> t
--     else throwError $ "wrong var name or ill typed variable usage"
--   DoneB _ -> throwError $ "variable out of scope"
--   ConsA _ (ConsA _ _) -> throwError $ "unused variables"
-- denoteTrans ctx codSpan (TransEApp r subTerms) =
--   unlist (resolveRef r) >>= \case
--   (SemTrans (ScopedSemTrans fCtx fCod transF)) -> do
--     -- first, exhibit the expected output type codSpan as an
--     -- instantiation of the functions type fCod
--     -- I.e. codSpan = quote (unquote fCod contraFun covarFun)

--     -- We need to infer this because even though we are being fairly
--     -- explicit in typing we are actually suppressing some information
--     -- from the term syntax: the most explicit form of the term
--     -- application would be something like (f A1 t1 A2 t2 A3 t3 A4)
--     -- rather than (f t1 t2 t3) here we are inferring A1 and A4. Later
--     -- we will need to infer the rest.
--     (contraFun, covarFun) <- codSpan `spanDecomposesInto` fCod
--     -- now check that the arguments are valid inputs to the
--     -- transformation
--     subst <- denoteTransSubst ctx contraFun covarFun fCtx subTerms
--     return $ transF . subst
--   _ -> throwError $ "expected a previously defined transformation, but got...something else"

-- denoteTransSubst :: NamedSemTransCtx -> EltNF -> EltNF -> SemTransCtx -> [TransExp] -> TCS ([TransNF] -> [TransNF])
-- denoteTransSubst domCtx contraFun covarFun codCtx es = do
--   (leftoverCtx, covarFun', composableSubst) <- denoteTransSubstComp domCtx contraFun codCtx es
--   case (leftoverCtx, covarFun == covarFun') of
--     (ConsA _ _, _) -> throwError $ "unused variables"
--     (_, False) -> throwError "some kind of mismatch, can this even happen?" -- TODO: write a better error message, when does this happen?
--     (DoneB _, True) -> return $ evalState composableSubst

-- denoteTransSubstComp :: NamedSemTransCtx -> EltNF -> SemTransCtx -> [TransExp] -> TCS (NamedSemTransCtx,EltNF, State [TransNF] [TransNF])
-- denoteTransSubstComp domCtx contraFun codCtx [] = case codCtx of
--   ConsA _ _ -> throwError $ "transformation applied to too few arguments"
--   DoneB _   -> return (domCtx, contraFun, return [])
-- denoteTransSubstComp domCtx contraFun codCtx (e:es) = case codCtx of
--   DoneB _ -> throwError $ "transformation applied to too many arguments"
--   ConsA (_,cod) codCtx -> do
--     (domCtx, contraFun, prefixEater) <- denoteTransSubstCons domCtx contraFun cod e
--     (domCtx, covarFun, suffixEater) <- denoteTransSubstComp domCtx contraFun codCtx es
--     return $ (domCtx, covarFun, (:) <$> prefixEater <*> suffixEater)

-- we are given the input context Phi ctx(a:C,-)
-- we know a substitution for the left side A : C => C'
-- and output span R span(a':C',=)

-- Given the term t,
-- we find the decomposition Phi_t,Phi_r = Phi
-- and the (most general?) function B
-- so that
--     Phi_t |- t : R[A;B]

-- and we return Phi_r, B and a denotation for t that returns both its
-- answer and the "leftover" args that it didn't consume
-- denoteTransSubstCons :: NamedSemTransCtx -> EltNF -> SpanNF -> TransExp -> TCS (NamedSemTransCtx,EltNF, State [TransNF] TransNF)
-- -- here we need to solve Phi_t |- x : R[A;B]
-- -- clearly we have Phi_t = alpha : C, x : R[A;B], beta : B
-- denoteTransSubstCons ctx contraFun codSpan (TransEVar x) = case ctx of
--   DoneB _ -> throwError $ "variable used, but none remain in the context"
--   ConsA (_,_,y,ySpan) ctx ->
--     if x /= y
--     then throwError $ "used the wrong variable"
--     else do
--       (contraFun', covarFun) <- codSpan `spanDecomposesInto` ySpan
--       guard $ contraFun == contraFun' -- | TODO: Is this necessary? When will it be wrong? Write an error msg for it
--       return $ (ctx, covarFun, f)
--         where
--           f :: State [TransNF] TransNF
--           f = do
--             (t:ts) <- get
--             put ts
--             return t

-- -- here we are solving
-- -- Phi_t |- f(t1,...,tn) : R[A;B]

-- denoteTransSubstCons ctx contraFun cod (TransEApp ref subterms) = unlist (resolveRef ref) >>= \case
-- -- first we lookup f's type and match it against R[A;B]
--   SemTrans (ScopedSemTrans fCtx fCod transF) -> do
--     (contraFun', covarFun) <- cod `spanDecomposesInto` fCod
--     guard $ contraFun' == contraFun -- TODO: will this ever error? write an error message if so
--     (ctx, covarFun', semArgs) <- denoteTransSubstComp ctx contraFun fCtx subterms
--     guard $ covarFun' == covarFun -- TODO: will this error either??
--     return (ctx, covarFun, transF <$> semArgs)
--   _ -> throwError $ "expected a previously defined transformation, but got...something else"
  

-- Unification time

-- special directed case of unification.  want to find an
-- instantiation of the second arg that makes it equal to the first.
spanDecomposesInto :: SpanNF -> SpanNF -> TCS (EltNF, EltNF)
(SNFSpanApp r1 f1 g1) `spanDecomposesInto` (SNFSpanApp r2 f2 g2) | r1 /= r2
  = throwError $ "transformation has wrong output span"
SNFSpanApp r1 f1 g1 `spanDecomposesInto` SNFSpanApp r2 f2 g2 -- | r1 == r2
  = (,) <$> (f1 `funDecomposesInto` f2) <*> (g1 `funDecomposesInto` g2)

-- f `fdi` g ~> h then f = quote (unquote g h)
funDecomposesInto :: EltNF -> EltNF -> TCS EltNF
e `funDecomposesInto` ENFId = return e
ENFId `funDecomposesInto` ENFFunApp f e = throwError $ "instantiation failure: a transformation was used whose type is too specific"
ENFFunApp f e `funDecomposesInto` ENFFunApp f' e' | f /= f' = throwError $ "instantiation failure: a transformation's type doesn't match its expected type"
ENFFunApp f e `funDecomposesInto` ENFFunApp f' e' = -- | f == f'
  ENFFunApp f <$> (e `funDecomposesInto` e')
  
-- denoteAndDeclare :: SynDecl ScopedExp -> TCS ()
-- denoteAndDeclare declaration = do
--   v <- denote $ _defn declaration
--   declare (declaration { _defn = v })

decl :: TC (SynDecl ScopedVal)
decl = list $
  tcSemDecl "def-mod" (SemMod <$> single modul)
  <|> tcSemDecl "def-set"   (SemSet   <$> single setVal)
  <|> tcSemDecl "def-fun"   (SemFun   <$> scopedFunVal)
  <|> tcSemDecl "def-span"  (SemSpan  <$> scopedSpanVal)
  <|> tcSemDecl "def-trans" (SemTrans <$> scopedTransVal)
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
-- or (M anyExpr ...)
modul :: TC ScopedSemMod
modul = modulVar
      <|> modulLam
  where
    modulVar = modDeref >>= \case
      SemMod m -> return m
      _ -> empty

    modulLam = enter . list $
      tcHd (atomEq "mod") *> do
      ps <- tcHd (list (several param))
      sig <- mayHd empty
      modBod <- moduleBody
      return $ ScopedSemMod () (ModNFBase ps (map undecl modBod))

    undecl (Decl a b) = (a,b)
  -- ModBase <$> modBase
  -- <|> ModApp <$> error ""

-- modExp :: TC ModExp -- | TODO: module lambda
-- modExp =
--   ModBase . GModVar <$> modDeref
--   <|> ModBase . GModLam <$> modLam -- <|> modApp parse don't check
--   where
--     -- modBase = ModBase <$>
--     --   ((GModVar . MDCurMod <$> modVar)
--     --    <|> GModLam <$> modLam)
--   --   modVar = do
--   --     var <- anyAtom
--   --     ctx <- get
--   --     case fmap isMod $ lookupSynDecl var ctx of
--   --       Just True -> return var
--   --       _ -> empty
--     modLam = localize $ list $
--       tcHd (atomEq "mod") >> do
--       params      <- tcHd (list params)
--       sigSynDecls <- mayHd sigExp
--       modBod      <- moduleBody
--       return $ ModLam params sigSynDecls modBod 
--   --   modApp = empty

setVal :: TC SetNF
setVal = modDeref >>= \case
  SemSet n -> return n
  _ -> throwError $ "expected a set, but got...something else"

-- setExp :: TC SetExp
-- setExp = modDeref

-- (x A) B t
scopedFunVal :: TCS ScopedSemFun
scopedFunVal = do
  (x, dom) <- tcHd eltVar
  cod <- tcHd setVal
  t <- single $ elt x dom cod
  return $ ScopedSemFun dom cod t

eltVar :: TC (String, SetNF)
eltVar = list $ (,) <$> tcHd anyAtom <*> single setVal

elt :: String -> SetNF -> SetNF -> TC EltNF
elt x dom cod =
  (atomEq x *> guard (dom == cod) *> return ENFId)
  <|> (list $ do
  f <- tcHd funVar
  guard $ cod == (f ^. scfunCod)
  arg <- single $ elt x dom (f ^. scfunDom)
  return $ unquoteSemFun (f ^. scfun) arg)
  where
    funVar = modDeref >>= \case
      SemFun f -> return f
      _ -> throwError $ "expected a function but gott...something else"

-- (x A) (y B) t
scopedSpanVal :: TCS ScopedSemSpan
scopedSpanVal = do
  (contraX, contraSet) <- tcHd eltVar
  (covarX,   covarSet) <- tcHd eltVar
  s <- single $ spanVal contraX contraSet covarX covarSet
  return $ ScopedSemSpan contraSet covarSet s

spanVal :: String -> SetNF -> String -> SetNF -> TC SpanNF
spanVal contraX contraSet covarX covarSet =
  list $ do
  r <- tcHd spanVar
  contraArg <- tcHd $ elt contraX contraSet (r ^. scspContra)
  covarArg  <- tcHd $ elt covarX  covarSet  (r ^. scspCovar)
  return $ unquoteSpan (r ^. scspan) contraArg covarArg
  where spanVar = modDeref >>= \case
          SemSpan r -> return r
          _ -> throwError "expected a span but got something else"

-- ((a X) (b Y) (c Z)) ((r (R a b)) (q (Q b c))) (P a c) bod
scopedTransVal :: TCS ScopedSemTrans
scopedTransVal = do
  indices <- tcHd $ spanStringIndices
  ctx     <- tcHd . list $ transCtx indices
  let ((contraX, contraSet), (covarX, covarSet)) = firstAndLast $ indices
  cod     <- tcHd $ spanVal contraX contraSet covarX covarSet
  ScopedSemTrans ctx cod <$> transValChk ctx cod

transCtx :: NEList (String, SetNF) -> TCS NamedSemTransCtx
transCtx (Done x)    = done $> DoneB x
transCtx (Cons (contraX, contraSet) indices) =
  let (covarX, covarSet) = indices ^. neHd in do
  (spanX, span) <- tcHd $ spanVarChk contraX contraSet covarX covarSet
  ConsA (contraX, contraSet, spanX, span) <$> transCtx indices

spanVarChk :: String -> SetNF -> String -> SetNF -> TC (String, SpanNF)
spanVarChk contraX contraSet covarX covarSet =
  list $ (,) <$> tcHd anyAtom <*> single (spanVal contraX contraSet covarX covarSet)

transValChk :: NamedSemTransCtx -> SpanNF -> TCS TransNF
transValChk doms cod = idVal <|> appVal
  where
    idVal = do
      x <- single anyAtom
      case doms of
        ConsA (_, _, y, r) (DoneB _) -> do
          guard $ x == y
          guard $ r == cod
          return $ TNFId
        (DoneB _) -> throwError "unbound transformation variable"
        (ConsA _ (ConsA _ _)) -> throwError "unused transformation variable(s)"
    appVal :: TCS TransNF
    appVal = empty

spanStringIndices :: TC (NEList (String, SetNF))
spanStringIndices = list (atLeastOne eltVar)

spanString :: NEList (String, SetNF) -> TCS SemTransCtx
spanString (Done x) = done $> DoneB (snd x)
spanString (Cons (contraVar, contraSet) xs) =
  let (covarVar, covarSet) = xs ^. neHd in do
  spn <- tcHd $ spanVal contraVar contraSet covarVar covarSet
  ConsA (contraSet, spn) <$> spanString xs
  
-- spanVar :: TC SpanVar
-- spanVar = list $ SpanVar <$> tcHd anyAtom <*> tcHd spanExp

-- scopedSpanExp :: TCS ScopedSpanExp      
-- scopedSpanExp = (,) <$> spanScope <*> single spanExp
--   where
--     spanScope = SpanScope <$> tcHd typedEltVar <*> tcHd typedEltVar

-- spanExp :: TC SpanExp
-- spanExp = list $ SpanEApp <$> tcHd modDeref <*> tcHd eltExp <*> tcHd eltExp

-- -- ((a A) ... ((x (R a b)) ...) (S a a') t)
-- scopedTransExp :: TCS ScopedTransExp
-- scopedTransExp = ScopedTransExp <$> transScope <*> single transExp
--   where transScope :: TCS TransScope
--         transScope = TransScope <$> tcHd (list $ atLeastOne typedEltVar) <*> tcHd (list $ several spanVar) <*> tcHd spanExp

--         transExp :: TC TransExp
--         transExp = TransEVar <$> anyAtom <|> list (TransEApp <$> tcHd modDeref <*> several transExp)

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

    select :: ScopedSemMod -> NEList String -> TCS ScopedVal
    select (ScopedSemMod sc mod) (Done s)    = selectOne sc mod s
    select (ScopedSemMod sc mod) (Cons s ss) = selectOne sc mod s >>= \case
      SemMod m -> select m ss

    selectOne :: Semantics.ModScope -> ModNF -> String -> TCS ScopedVal
    selectOne sc (ModNFApp db vs)     s = error "NYI: quantification over modules"
    selectOne sc (ModNFBase (_:_) ds) s = throwError "Tried to select from a parameterized module that is not fully applied"
    selectOne sc (ModNFBase [] ds) s = case lookup s ds of
      Nothing -> error "Tried to select a value not in the module"
      Just x  -> return x

-- | check the generator for validity and then add the declaration to
-- the context

nextDB :: TCS DBRef
nextDB = DBCurMod <$> (_2 . numParams <<+= 1)

-- curDB :: TCS Int
-- curDB = subtract 1 . length <$> ctx

denoteGenerator :: Type -> TCS ScopedVal
denoteGenerator ty = flip dbVal ty <$> nextDB

-- denoteGenerator :: Generator -> TCS ScopedVal
-- denoteGenerator = \case
--   GenSet -> SemSet . DBCurMod <$> nextDB
--   GenFun eltty -> do
--     dom <- denoteSet $ _eltdomty eltty
--     cod <- denoteSet $ _eltcodty eltty
--     funName <- nextDB
--     return $ SemFun (ScopedSemFun dom cod (ENFFunApp (DBCurMod funName) ENFId))
--   GenSpan spanty -> do
--     contravar <- denoteSet $ _spancontraty spanty
--     covar     <- denoteSet $ _spancoty     spanty
--     spanName <- nextDB
--     return $ SemSpan (ScopedSemSpan contravar covar (SNFSpanApp (DBCurMod spanName) ENFId ENFId))
--   GenTrans transty -> do
--     -- setIndices :: [(String, SetNF)]
--     setIndices <- traverse (traverse denoteSet . topair) (_eltVars $ transty)
--     transCtx <-
--       ctxUnName <$> denoteSpanString setIndices (map (SpanVar "dummy") $ _domSpans transty)
--     let len = length . ctxSpans $ transCtx
--     let ((x, contraty), (y, covarty)) = firstAndLast setIndices
--     codSpan <- denoteSpan x contraty y covarty (_codSpan transty)
--     name <- nextDB
--     return $
--       SemTrans (ScopedSemTrans transCtx codSpan
--                                (TNFApp (DBCurMod name) . take len))
--       where topair x = (_eltvar x, _eltvarty x)
            
    -- first validate the type
-- case _defn declGen of
--   GenSet -> do
--     ix <- nextDB
--     return (declGen { _defn = _ })
--   _      -> _

declareGenerator :: SynDecl Type -> TCS Type
declareGenerator declGen = do
  declare =<< defn denoteGenerator declGen
  return $ declGen ^. defn
    
-- | Has the effect of extending the current context
param :: TC Type
param = list $
  (genName "set" (done $> TypeSet))
  <|> genName "fun"   (TypeFun  <$> tcHd setVal <*> tcHd setVal <* done)
  <|> genName "span"  (TypeSpan <$> tcHd setVal <*> tcHd setVal <* done)
  -- (trans t ((a X) (b Y) (c Z) (d W)) ((R a b) (S b c) (Q d c)) (P a d))
  <|> genName "trans" (do
      indices <- tcHd spanStringIndices
      ctx <- tcHd . list $ spanString indices
      let ((contraX, contraSet), (covarX, covarSet)) = firstAndLast $ indices
      cod <- single (spanVal contraX contraSet covarX covarSet)
      return $ TypeTrans ctx cod)
  where
    genName key p = declareGenerator =<< ((tcHd (atomEq key)) *> (Decl <$> tcHd anyAtom <*> p))

  -- | GenSet -- "base type"                        (set X)
  -- | GenFun EltScope -- "function symbol"         (fun f A B)
  -- | GenSpan SpanScope -- "base type constructor" (span R A B)
  -- | GenTrans TransScope -- "function symbol"     (fun F Delta Phi R)
  -- Delta = ((a A) ...)
  -- Phi   = ((x R) ...)
  -- | and an axiom one too...
