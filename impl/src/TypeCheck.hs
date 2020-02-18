{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TypeCheck where

import Control.Applicative
import Data.Functor
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import Data.Foldable
import Data.Traversable
import Grammar

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

type ErrMsg = String

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
  fmap fst $ runIdentity $ runExceptT $ runStateT m (exps, [])

typeCheckOne :: TC a -> ParsedSExp -> Either String a
typeCheckOne (TC m) exp =
  fmap fst $ runIdentity $ runExceptT $ runStateT (runReaderT m exp) []

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
    [] -> throwError "expected another thing but there was nothing left :("
    (x:xs) -> do
      (a, ctx) <- runStateT (runReaderT (runTC p) $ x) ctx
      return (a, (xs,ctx))

-- ensure there's nothing left
done :: TCS ()
done = fst <$> get >>= \case
  [] -> return ()
  _  -> throwError "there's some junk here"
  

only :: TC a -> TCS a
only p = tcHd p <* done
  
-- "hanndle" the reader effect using the state effect?
list :: TCS a -> TC a
list k = TC . ReaderT $ \sexp -> StateT $ \ctx -> case _sexp sexp of
  SEAtom a -> throwError $ "expected a list but got" ++ a
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
  SEList _ -> throwError "got a list, wanted an atom"

atomEq  :: String -> TC ()
atomEq s = do
  at <- anyAtom
  guard $ at == s

program :: TCS Program
program = moduleBody

moduleBody :: TCS ModuleBody
moduleBody = ModuleBody <$> (several decl)

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
  (ScFun e) -> (\(dom,cod,f) -> SemFun dom cod f) <$> denoteFun e

denoteSet :: SetExp -> TCS SetNF
denoteSet mdref = do
  (Decl _ (SemSet dbref)) <- resolveRef mdref
  return dbref

denoteFun :: ScopedEltExp -> TCS (SetNF, SetNF, (EltNF -> EltNF))
denoteFun (ScopedEltExp (EltScope (TypedEltVar x domTyExp) codTyExp) e) = do
  dom <- denoteSet domTyExp
  cod <- denoteSet codTyExp
  f <- loop x dom cod e
  return (dom,cod,f)
  where
    loop :: String -> SetNF -> SetNF -> EltExp -> TCS (EltNF -> EltNF)
    loop x dom cod (EEVar y) = do
      guard $ x == y
      guard $ dom == cod
      return (\nf -> nf)
    loop x dom cod (EEApp ref e) = do
      (Decl _ (SemFun dom' cod' f)) <- resolveRef ref
      guard $ cod == cod'
      g <- loop x dom dom' e
      return (f . g)

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
  -- (def-fun f (x A) B
  --   e)
--  <|> tcSynDecl "def-fun" ()
  -- TODO: fun, span, trans, assertion
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
      params   <- tcHd (list params)
      sigSynDecls <- resolveSignature =<< tcHd sigExp
      modBod   <- moduleBody
      guard $ (modBod `fulfilsSig` sigSynDecls)
      return $ ModLam params sigSynDecls modBod 
  --   modApp = empty

-- | TODO: impl
resolveSignature :: SigExp -> TCS [SynDecl Generator]
resolveSignature s = return []

-- | TODO: impl
fulfilsSig :: ModuleBody -> [SynDecl Generator] -> Bool
fulfilsSig modBod sig = True
  
setExp :: TC SetExp
setExp = modDeref -- TODO: add mod deref

-- (x A) B t
scopedEltExp :: TCS ScopedEltExp
scopedEltExp = ScopedEltExp <$> eltScope <*> only eltExp
  where
    eltScope    = EltScope <$> tcHd typedEltVar <*> tcHd setExp
    typedEltVar = list $ TypedEltVar <$> tcHd anyAtom <*> tcHd setExp

    eltExp = EEVar <$> anyAtom
             <|> list (EEApp <$> tcHd modDeref <*> tcHd eltExp)

  --   checkElt :: EltScope -> EltExp -> TCS ()
  --   checkElt types (EEVar x) = guard $ (_eltvar . _eltinp $ types) == x
  --   checkElt types (EEApp (MDCurMod f) e) = do
  --     ctx <- snd <$> get
  --     let Just eltty = getFunTy =<< lookupSynDecl f ctx
  --     guard $ _eltcodty eltty == _eltty types
  --     checkElt (types { _eltty = _eltdomty eltty }) e
      


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
    return $ SemFun dom cod (ENFFunApp (DBCurMod funName))
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
  where
    genName keyword p = tcHd (atomEq keyword) >> Decl <$> tcHd anyAtom <*> p
  -- | GenSet -- "base type"                        (set X)
  -- | GenFun EltScope -- "function symbol"         (fun f A B)
  -- | GenSpan SpanScope -- "base type constructor" (span R A B)
  -- | GenTrans TransScope -- "function symbol"     (fun f Phi R)
  -- | and an axiom one too...
