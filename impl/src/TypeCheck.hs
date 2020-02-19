{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module TypeCheck where

import Control.Applicative
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

import Grammar
import Util

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

newtype ErrMsg = ErrMsg { _getMsg :: First String }
  deriving (Show, Read, Eq, Monoid)

instance IsString ErrMsg where
  fromString = ErrMsg . First . Just

ctx :: TCS Ctx
ctx = snd <$> get

popDecl :: TCS (SynDecl SemVal)
popDecl = do
  (p, ctx) <- get
  case ctx of
    [] -> throwError $ "unbound variable"
    (d:rest) -> do
      put (p, rest)
      return d

typeCheck :: TCS a -> [ParsedSExp] -> Either String a
typeCheck (TCS m) exps =
  lErrToStr .  fmap fst $ runIdentity $ runExceptT $ runStateT m (exps, [])
  

typeCheckOne :: TC a -> ParsedSExp -> Either String a
typeCheckOne (TC m) exp =
  lErrToStr . fmap fst $ runIdentity $ runExceptT $ runStateT (runReaderT m exp) []

lErrToStr = either (Left . errToStr) Right

errToStr :: ErrMsg -> String
errToStr (ErrMsg (First Nothing)) = "internal error: no cases"
errToStr (ErrMsg (First (Just s))) = s

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
  

only :: TC a -> TCS a
only p = tcHd p <* done
  
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
moduleBody = ModuleBody <$> ((several decl) <|> (throwError $ "expected a sequence of declaration"))

declare :: SynDecl SemVal -> TCS ()
declare d = modify (fmap (d:))

sideeffect :: Monad m => (a -> m ()) -> m a -> m a
sideeffect k m = do
  x <- m
  k x
  return x

resolveRef :: ModDeref -> TCS (Decl DBRef SemVal)
resolveRef (MDSelect _ _) = error "NYI: submodules"
resolveRef (MDCurMod s) = localize (resolveCurMod s =<< curDB)
  where
    resolveCurMod :: String -> Int -> TCS (Decl DBRef SemVal)
    resolveCurMod s db = do
      decl <- popDecl
      if _name decl == s
        then return $ decl { _name = DBCurMod db }
        else resolveCurMod s (subtract 1 db)

denote :: ScopedExp -> TCS SemVal
denote = \case 
  (ScMod _) -> return SemMod
  (ScSet e) -> SemSet <$> denoteSet e
  (ScFun e) -> SemFun <$> denoteScopedFun e
  (ScSpan e) -> SemSpan <$> denoteScopedSpan e
  (ScTrans e) -> SemTrans <$> denoteScopedTrans e

denoteSet :: SetExp -> TCS SetNF
denoteSet mdref = do
  (Decl _ val) <- resolveRef mdref
  case val of
    (SemSet dbref) -> return dbref
    _ -> throwError $ "expected a set but got...something else"

denoteScopedFun :: ScopedEltExp -> TCS ScopedSemFun
denoteScopedFun (ScopedEltExp (EltScope (TypedEltVar x domTyExp) codTyExp) e) = do
  dom <- denoteSet domTyExp
  cod <- denoteSet codTyExp
  f <- denoteFun x dom cod e
  return (ScopedSemFun dom cod f)
  where

denoteFun :: String -> SetNF -> SetNF -> EltExp -> TCS (EltNF -> EltNF)
denoteFun x dom cod (EEVar y) = do
      guard $ x == y
      guard $ dom == cod
      return (\nf -> nf)
denoteFun x dom cod (EEApp ref e) = do
      (Decl _ val) <- resolveRef ref
      case val of
        (SemFun (ScopedSemFun dom' cod' f)) -> do
          guard $ cod == cod'
          g <- denoteFun x dom dom' e
          return (f . g)
        _ -> throwError $ "expected a function but got...something else"

denoteScopedSpan :: ScopedSpanExp -> TCS ScopedSemSpan
denoteScopedSpan (SpanScope (TypedEltVar x contraSetExp) (TypedEltVar y covarSetExp) , e) = do
  contraSetDom <- denoteSet contraSetExp
  covarSetDom <- denoteSet covarSetExp
  semspan <- denoteSpan x contraSetDom y covarSetDom e
  return $ ScopedSemSpan contraSetDom covarSetDom semspan

denoteSpan :: String -> SetNF -> String -> SetNF -> SpanExp -> TCS (EltNF -> EltNF -> SpanNF)
denoteSpan x contraSetDom y covarSetDom (SpanEApp ref a b) = do
  (Decl _ val) <- resolveRef ref
  case val of
    (SemSpan (ScopedSemSpan contraSetCod covarSetCod spanfun')) -> do
      contraFun <- denoteFun x contraSetDom contraSetCod a
      covarFun  <- denoteFun y covarSetDom covarSetCod b
      return $ \contra covar -> spanfun' (contraFun contra) (covarFun covar)
    _ -> throwError $ "expected a span constructor but got...something else"

denoteSpanString :: NEList (String, SetNF) -> [SpanExp] -> TCS SemTransCtx
denoteSpanString (Done (_, covarset)) [] = return $ DoneB covarset
denoteSpanString (Cons (x, contraset) vars) (e : es) = do
  span <- quoteSemSpan <$> denoteSpan x contraset y covarset e
  ConsA (contraset, span) <$> denoteSpanString vars es
  where (y, covarset) = neHd vars
denoteSpanString (Done _) (e : es) = throwError $ "not enough indices for the inputs of a transformation"
denoteSpanString (Cons _ _) [] = throwError $ "too many indices for the inputs of a transformation"

denoteScopedTrans :: ScopedTransExp -> TCS ScopedSemTrans
denoteScopedTrans e = empty -- TODO

-- this will probably have to change to do some inference when we add
-- positive types (hom/tensor), though probably not when we add
-- negative types like cotensor/products/pullbacks
denoteTrans :: NamedSemTransCtx -> SpanNF -> TransExp -> TCS ([TransNF] -> TransNF)
denoteTrans ctx codSpan (TransEVar x) = case ctx of
  ConsA (alphaContra, contraSet, spanVar, domSpan) (DoneB (betaCovar, covarSet)) ->
    if x == spanVar && codSpan == domSpan
    then return $ \[t] -> t
    else throwError $ "wrong var name or ill typed variable usage"
  DoneB _ -> throwError $ "variable out of scope"
  ConsA _ (ConsA _ _) -> throwError $ "unused variables"
denoteTrans ctx codSpan (TransEApp r args) =
  resolveRef r >>= \case
  Decl _ (SemTrans (ScopedSemTrans fCtx fCod transF)) -> do
    (contraFun, covarFun) <- codSpan `spanDecomposesInto` fCod
    -- first, unify the codomain of the transformation with the expected codomain
    _
  _ -> throwError $ "expected a previously defined transformation, but got...something else"


-- Unification time

-- special directed case of unification. The first input is
-- parameterized by two inputs and we want to find a substitution for
-- those inputs that would make it equal to the second argument.
spanDecomposesInto :: SpanNF -> SpanNF -> TCS (EltNF, EltNF)
SNFSpanApp r1 f1 g1 `spanDecomposesInto` SNFSpanApp r2 f2 g2 | r1 /= r2
  = throwError $ "transformation has wrong output span"
SNFSpanApp r1 f1 g1 `spanDecomposesInto` SNFSpanApp r2 f2 g2 | r1 == r2
  = (,) <$> (f1 `funDecomposesInto` f2) <*> (g1 `funDecomposesInto` g2)


funDecomposesInto :: EltNF -> EltNF -> TCS EltNF
ENFId `funDecomposesInto` e = return e
ENFFunApp f e `funDecomposesInto` ENFId = throwError $ "instantiation failure: a transformation was used whose type is too specific"
ENFFunApp f e `funDecomposesInto` ENFFunApp f' e' | f /= f' = throwError $ "instantiation failure: a transformation's type doesn't match its expected type"
ENFFunApp f e `funDecomposesInto` ENFFunApp f' e' | f == f' =
  ENFFunApp f <$> (e `funDecomposesInto` e')
  
denoteAndDeclare :: SynDecl ScopedExp -> TCS ()
denoteAndDeclare declaration = do
  v <- denote $ _defn declaration
  declare (declaration { _defn = v })

decl :: TC (SynDecl ScopedExp)
decl = list . sideeffect denoteAndDeclare $
      -- tcSynDecl "def-sig" (ScSig <$> only sigExp)
  tcSynDecl "def-mod" (ScMod <$> only modExp)
  <|> tcSynDecl "def-set" (ScSet <$> only setExp)
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
sigExp = return dummy
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
scopedEltExp = ScopedEltExp <$> eltScope <*> only eltExp
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
scopedSpanExp = (,) <$> spanScope <*> only spanExp
  where
    spanScope = SpanScope <$> tcHd typedEltVar <*> tcHd typedEltVar

spanExp :: TC SpanExp
spanExp = list $ SpanEApp <$> tcHd modDeref <*> tcHd eltExp <*> tcHd eltExp

-- ((a A) ... ((x (R a b)) ...) (S a a') t)
scopedTransExp :: TCS ScopedTransExp
scopedTransExp = ScopedTransExp <$> transScope <*> only transExp
  where transScope :: TCS TransScope
        transScope = TransScope <$> tcHd (list $ several typedEltVar) <*> tcHd (list $ several spanVar) <*> tcHd spanExp

        transExp :: TC TransExp
        transExp = TransEVar <$> anyAtom <|> list (TransEApp <$> tcHd modDeref <*> several transExp)

modDeref :: TC ModDeref
modDeref = MDCurMod <$> anyAtom
           -- <|> selector -- TODO: implement selectors

params :: TCS [SynDecl Generator]
params = several param

-- | check the generator for validity and then add the declaration to
-- the context

-- | TODO: improve the repr so this isn't linear
nextDB :: TCS Int
nextDB = length <$> ctx

curDB :: TCS Int
curDB = subtract 1 . length <$> ctx

denoteGenerator :: Generator -> TCS SemVal
denoteGenerator = \case
  GenSet -> SemSet . DBCurMod <$> nextDB
  GenFun eltty -> do
    dom <- denoteSet $ _eltdomty eltty
    cod <- denoteSet $ _eltcodty eltty
    funName <- nextDB
    return $ SemFun (ScopedSemFun dom cod (ENFFunApp (DBCurMod funName)))
  GenSpan spanty -> do
    contravar <- denoteSet $ _spancontraty spanty
    covar     <- denoteSet $ _spancoty     spanty
    spanName <- nextDB
    return $ SemSpan (ScopedSemSpan contravar covar (SNFSpanApp (DBCurMod spanName)))
  GenTrans transty -> do
    -- setIndices :: [(String, SetNF)]
    rawSetIndices <- traverse (traverse denoteSet . topair) (_eltVars $ transty)
    case toNE rawSetIndices of
      Nothing -> throwError $ "expected at least one index in a span"
      Just setIndices -> do
        transCtx <- denoteSpanString setIndices (_domSpans transty)
        let len = length . ctxSpans $ transCtx
        let ((x, contraty), (y, covarty)) = firstAndLast setIndices
        codSpan <- quoteSemSpan <$> denoteSpan x contraty y covarty (_codSpan transty)
        name <- nextDB
        return $
          SemTrans (ScopedSemTrans transCtx codSpan
                                   (TNFApp (DBCurMod name) . take len))
      where topair x = (_eltvar x, _eltvarty x)
            
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
  <|> genName "trans" (GenTrans <$> (TransTy <$> tcHd (list (several typedEltVar)) <*> tcHd (list (several spanExp)) <*> tcHd spanExp))
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
