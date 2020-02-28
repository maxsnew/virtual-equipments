{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
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
  
several :: TC a -> TCS [a]
several tc = ([] <$ done) <|> ((:) <$> tcHd tc <*> several tc)

atLeastOne :: TC a -> TCS (NEList a)
atLeastOne p = ((Done <$> tcHd p) <* done) <|> (Cons <$> tcHd p <*> atLeastOne p)

-- slurpAll :: TCS ()
-- slurpAll = _2 .= []

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

program :: TCS Program
program = moduleBody

moduleBody :: TCS ModuleBody
moduleBody = ModuleBody <$> ((several decl) <|> empty)

declare :: SynDecl ScopedVal -> TCS ()
declare d = (_2 . localBindings) %= (d:)

sideeffect :: Monad m => (a -> m ()) -> m a -> m a
sideeffect k m = do
  x <- m
  k x
  return x

resolveRef :: ModDeref -> TCS ScopedVal
resolveRef (MDSelect _ _) = error "NYI: submodules"
resolveRef (MDCurMod s) = (resolveBinding s) =<< (get <&> view _2)
  where
    resolveBinding :: String -> Ctx -> TCS ScopedVal
    resolveBinding s c = case c ^. localBindings of
      []   -> case c ^? restCtx of
        Nothing -> throwError $ "unbound variable"
        Just rest -> shiftVal <$> resolveBinding s rest
      b:bs ->
        if _name b == s
        then return $ _defn b
        else resolveBinding s (c & localBindings .~ bs)

denote :: ScopedExp -> TCS ScopedVal
denote = \case 
  (ScMod e) -> SemMod . ScopedSemMod <$> denoteMod e
  (ScSet e) -> SemSet <$> denoteSet e
  (ScFun e) -> SemFun <$> denoteScopedFun e
  (ScSpan e) -> SemSpan <$> denoteScopedSpan e
  (ScTrans e) -> error "NYI: trans" -- SemTrans <$> denoteScopedTrans e

denoteMod :: ModExp -> TCS ([ScopedVal] -> [ScopedVal])
denoteMod (ModBase (GModLam l)) = denoteModLam l

denoteModLam :: ModLambda -> TCS ([ScopedVal] -> [ScopedVal])
denoteModLam (ModLam params _ bod) = return (\x -> error "NYI: module lambda")

denoteSet :: SetExp -> TCS SetNF
denoteSet mdref = resolveRef mdref >>= \case
  (SemSet dbref) -> return dbref
  _ -> throwError $ "expected a set but got...something else"

denoteScopedFun :: ScopedEltExp -> TCS ScopedSemFun
denoteScopedFun (ScopedEltExp (EltScope (TypedEltVar x domTyExp) codTyExp) e) = do
  dom <- denoteSet domTyExp
  cod <- denoteSet codTyExp
  f <- denoteFun x dom cod e
  return (ScopedSemFun dom cod f)
  where

denoteFun :: String -> SetNF -> SetNF -> EltExp -> TCS EltNF
denoteFun x dom cod (EEVar y) = do
      guard $ x == y
      guard $ dom == cod
      return ENFId
denoteFun x dom cod (EEApp ref e) = resolveRef ref >>= \case
        (SemFun (ScopedSemFun dom' cod' f)) -> do
          guard $ cod == cod'
          g <- denoteFun x dom dom' e
          return $ unquoteSemFun f g
        _ -> throwError $ "expected a function but got...something else"

denoteScopedSpan :: ScopedSpanExp -> TCS ScopedSemSpan
denoteScopedSpan (SpanScope (TypedEltVar x contraSetExp) (TypedEltVar y covarSetExp) , e) = do
  contraSetDom <- denoteSet contraSetExp
  covarSetDom <- denoteSet covarSetExp
  semspan <- denoteSpan x contraSetDom y covarSetDom e
  return $ ScopedSemSpan contraSetDom covarSetDom semspan

denoteSpan :: String -> SetNF -> String -> SetNF -> SpanExp -> TCS SpanNF
denoteSpan x contraSetDom y covarSetDom (SpanEApp ref a b) = resolveRef ref >>= \case
    (SemSpan (ScopedSemSpan contraSetCod covarSetCod span)) -> do
      contraFun <- denoteFun x contraSetDom contraSetCod a
      covarFun  <- denoteFun y covarSetDom covarSetCod b
      return $ unquoteSpan span contraFun covarFun
    _ -> throwError $ "expected a span constructor but got...something else"

-- denoteSpanString :: NEList (String, SetNF) -> [SpanVar] -> TCS NamedSemTransCtx
-- denoteSpanString (Done tvar) [] = return $ DoneB tvar
-- denoteSpanString (Cons (contravar, contraset) vars) ((SpanVar spanVar spanE) : es) = do
--   span <- quoteSemSpan <$> denoteSpan contravar contraset covarvar covarset spanE
--   ConsA (contravar, contraset, spanVar, span) <$> denoteSpanString vars es
--   where (covarvar, covarset) = neHd vars
-- denoteSpanString (Done _) (e : es) = throwError $ "not enough indices for the inputs of a transformation"
-- denoteSpanString (Cons _ _) [] = throwError $ "too many indices for the inputs of a transformation"

-- denoteScopedTrans :: ScopedTransExp -> TCS ScopedSemTrans
-- denoteScopedTrans (ScopedTransExp (TransScope indicesE varsE codE) e) = do
--   indices <- traverse (\tvar -> (,) (_eltvar tvar) <$> denoteSet (_eltvarty tvar)) indicesE
--   ctx <- denoteSpanString indices varsE
--   let ((contravar, contraty), (covarvar, covarty)) = firstAndLast indices
--   cod <- quoteSemSpan <$> denoteSpan contravar contraty covarvar covarty codE
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
--   resolveRef r >>= \case
--   Decl _ (SemTrans (ScopedSemTrans fCtx fCod transF)) -> do
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

-- -- we are given the input context Phi ctx(a:C,-)
-- -- we know a substitution for the left side A : C => C'
-- -- and output span R span(a':C',=)

-- -- Given the term t,
-- -- we find the decomposition Phi_t,Phi_r = Phi
-- -- and the (most general?) function B
-- -- so that
-- --     Phi_t |- t : R[A;B]

-- -- and we return Phi_r, B and a denotation for t that returns both its
-- -- answer and the "leftover" args that it didn't consume
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

-- denoteTransSubstCons ctx contraFun cod (TransEApp ref subterms) = resolveRef ref >>= \case
-- -- first we lookup f's type and match it against R[A;B]
--   Decl _ (SemTrans (ScopedSemTrans fCtx fCod transF)) -> do
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
  
denoteAndDeclare :: SynDecl ScopedExp -> TCS ()
denoteAndDeclare declaration = do
  v <- denote $ _defn declaration
  declare (declaration { _defn = v })

decl :: TC (SynDecl ScopedExp)
decl = list . sideeffect denoteAndDeclare $
      -- tcSynDecl "def-sig" (ScSig <$> single sigExp)
  tcSynDecl "def-mod" (ScMod <$> single modExp)
  <|> tcSynDecl "def-set" (ScSet <$> single setExp)
  <|> tcSynDecl "def-fun" (ScFun <$> scopedEltExp)
  <|> tcSynDecl "def-span" (ScSpan <$> scopedSpanExp)
  <|> tcSynDecl "def-trans" (ScTrans <$> scopedTransExp)
  -- (def-trans t (a b c d) (Rab Sbc Qcd) Tad bod)
  -- TODO: trans, assertion
  where
    tcSynDecl :: String -> TCS a -> TCS (SynDecl a)
    tcSynDecl def p = (tcHd (atomEq def) >> Decl <$> tcHd anyAtom <*> p)

-- (sig () param ...) -- sig value
-- (sig (param param ...) param ...) -- sig lambda
-- or S
-- or (S ...)
-- or (. C ...)

sigExp :: TC SigExp
sigExp = list $ tcHd (atomEq "sig") >> return dummy
  where dummy = SigBase . GSigVar $ "NYI"
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
modExp :: TC ModExp -- | TODO: module lambda
modExp = ModBase . GModLam <$> modLam -- <|> modApp parse don't check
  where
    -- modBase = ModBase <$>
    --   ((GModVar . MDCurMod <$> modVar)
    --    <|> GModLam <$> modLam)
  --   modVar = do
  --     var <- anyAtom
  --     ctx <- get
  --     case fmap isMod $ lookupSynDecl var ctx of
  --       Just True -> return var
  --       _ -> empty
    modLam = localize $ list $
      tcHd (atomEq "mod") >> do
      params      <- tcHd (list params)
      sigSynDecls <- mayHd sigExp
      modBod      <- moduleBody
      return $ ModLam params sigSynDecls modBod 
  --   modApp = empty

setExp :: TC SetExp
setExp = modDeref -- TODO: add mod deref

-- (x A) B t
scopedEltExp :: TCS ScopedEltExp
scopedEltExp = ScopedEltExp <$> eltScope <*> single eltExp
  where
    eltScope    = EltScope <$> tcHd typedEltVar <*> tcHd setExp

eltExp :: TC EltExp
eltExp = EEVar <$> anyAtom
         <|> list (EEApp <$> tcHd modDeref <*> tcHd eltExp)

typedEltVar :: TC TypedEltVar
typedEltVar = list $ TypedEltVar <$> tcHd anyAtom <*> tcHd setExp

spanVar :: TC SpanVar
spanVar = list $ SpanVar <$> tcHd anyAtom <*> tcHd spanExp

-- (x A) (y B) t
scopedSpanExp :: TCS ScopedSpanExp      
scopedSpanExp = (,) <$> spanScope <*> single spanExp
  where
    spanScope = SpanScope <$> tcHd typedEltVar <*> tcHd typedEltVar

spanExp :: TC SpanExp
spanExp = list $ SpanEApp <$> tcHd modDeref <*> tcHd eltExp <*> tcHd eltExp

-- ((a A) ... ((x (R a b)) ...) (S a a') t)
scopedTransExp :: TCS ScopedTransExp
scopedTransExp = ScopedTransExp <$> transScope <*> single transExp
  where transScope :: TCS TransScope
        transScope = TransScope <$> tcHd (list $ atLeastOne typedEltVar) <*> tcHd (list $ several spanVar) <*> tcHd spanExp

        transExp :: TC TransExp
        transExp = TransEVar <$> anyAtom <|> list (TransEApp <$> tcHd modDeref <*> several transExp)

modDeref :: TC ModDeref
modDeref = MDCurMod <$> anyAtom
           -- <|> selector -- TODO: implement selectors

params :: TCS [SynDecl Generator]
params = several param

-- | check the generator for validity and then add the declaration to
-- the context

nextDB :: TCS Int
nextDB = _2 . numParams <<+= 1

-- curDB :: TCS Int
-- curDB = subtract 1 . length <$> ctx

denoteGenerator :: Generator -> TCS ScopedVal
denoteGenerator = \case
  GenSet -> SemSet . DBCurMod <$> nextDB
  GenFun eltty -> do
    dom <- denoteSet $ _eltdomty eltty
    cod <- denoteSet $ _eltcodty eltty
    funName <- nextDB
    return $ SemFun (ScopedSemFun dom cod (ENFFunApp (DBCurMod funName) ENFId))
  GenSpan spanty -> do
    contravar <- denoteSet $ _spancontraty spanty
    covar     <- denoteSet $ _spancoty     spanty
    spanName <- nextDB
    return $ SemSpan (ScopedSemSpan contravar covar (SNFSpanApp (DBCurMod spanName) ENFId ENFId))
  GenTrans transty -> error "NYI: trans"

    -- do
    -- -- setIndices :: [(String, SetNF)]
    -- setIndices <- traverse (traverse denoteSet . topair) (_eltVars $ transty)
    -- transCtx <-
    --   ctxUnName <$> denoteSpanString setIndices (map (SpanVar "dummy") $ _domSpans transty)
    -- let len = length . ctxSpans $ transCtx
    -- let ((x, contraty), (y, covarty)) = firstAndLast setIndices
    -- codSpan <- quoteSemSpan <$> denoteSpan x contraty y covarty (_codSpan transty)
    -- name <- nextDB
    -- return $
    --   SemTrans (ScopedSemTrans transCtx codSpan
    --                            (TNFApp (DBCurMod name) . take len))
    --   where topair x = (_eltvar x, _eltvarty x)
            
    -- first validate the type
-- case _defn declGen of
--   GenSet -> do
--     ix <- nextDB
--     return (declGen { _defn = _ })
--   _      -> _

declareGenerator :: SynDecl Generator -> TCS ()
declareGenerator declGen = do
  v <- denoteGenerator (_defn declGen)
  declare (declGen { _defn = v })
    
    
-- | Warning: this has the effect of extending the current context
param :: TC (SynDecl Generator)
param = list . sideeffect (declareGenerator) $
      genName "set" (done $> GenSet)
  <|> genName "fun"  (GenFun  <$> (EltTy  <$> tcHd setExp <*> tcHd setExp <* done))
  <|> genName "span" (GenSpan <$> (SpanTy <$> tcHd setExp <*> tcHd setExp <* done))
  <|> genName "trans" (GenTrans <$> (TransTy <$> tcHd (list (atLeastOne typedEltVar)) <*> tcHd (list (several spanExp)) <*> tcHd spanExp))
  -- (def-trans t (a b c d) (Rab Sbc Qcd) Tad bod)
  where
    genName keyword p = tcHd (atomEq keyword) >> Decl <$> tcHd anyAtom <*> p
  -- | GenSet -- "base type"                        (set X)
  -- | GenFun EltScope -- "function symbol"         (fun f A B)
  -- | GenSpan SpanScope -- "base type constructor" (span R A B)
  -- | GenTrans TransScope -- "function symbol"     (fun F Delta Phi R)
  -- Delta = ((a A) ...)
  -- Phi   = ((x R) ...)
  -- | and an axiom one too...
