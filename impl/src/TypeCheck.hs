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

-- we're either parsing a sequence, or inspecting a single sexp
-- either err (s -> (s,a))
-- s -> (s, either err a)
-- s -> either err (s, a)

newtype TCS a = TCS { runTCS :: StateT ([ParsedSExp], Ctx) (ExceptT ErrMsg Identity) a }
  deriving (Functor,Applicative,Monad,Alternative,MonadError ErrMsg, MonadState ([ParsedSExp], Ctx))

newtype TC a = TC { runTC :: ReaderT ParsedSExp (StateT Ctx (ExceptT ErrMsg Identity)) a }
  deriving (Functor,Applicative,Monad,Alternative,MonadError ErrMsg, MonadReader ParsedSExp, MonadState Ctx)

type ErrMsg = String

typeCheck :: TCS a -> [ParsedSExp] -> Either String a
typeCheck (TCS m) exps =
  fmap fst $ runIdentity $ runExceptT $ runStateT m (exps, [])

typeCheckOne :: TC a -> ParsedSExp -> Either String a
typeCheckOne (TC m) exp =
  fmap fst $ runIdentity $ runExceptT $ runStateT (runReaderT m exp) []

localize :: TC a -> TC a
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

declare :: Decl DeforGen -> TCS ()
declare d = modify (fmap (d:))

sideeffect :: Monad m => (a -> m ()) -> m a -> m a
sideeffect k m = do
  x <- m
  k x
  return x

decl :: TC (Decl ScopedExp)
decl = list . sideeffect (declare . fmap DGExp) $
      tcDecl "def-sig" (ScSig <$> sigExp)
  <|> tcDecl "def-mod" (ScMod <$> modExp)
  where
    tcDecl :: String -> TCS a -> TCS (Decl a)
    tcDecl def p = (tcHd (atomEq def) >> Decl <$> tcHd anyAtom <*> p)

-- (sig (param ...) param ...)
-- or S
-- or (S ...)
-- or (. C ...)

sigExp :: TCS SigExp
sigExp = only (sigBase <|> sigApp)
  where
    sigBase = SigBase <$> (GSigVar <$> sigVar <|> GSigLam <$> sigLam)
    sigVar  = do
      var <- anyAtom
      ctx <- get
      case fmap isSig $ lookupDecl var ctx of
        Just True -> return var
        _ -> empty
    sigLam = localize $ list $ tcHd (atomEq "sig") >> SigLam <$> tcHd (list params) <*> params
    sigApp :: TC SigExp
    sigApp = empty -- TODO: signature application

-- (mod (param ...) sig param ...)
-- or C
-- or (. C ...)
-- or (M anyExpr ...)
modExp :: TCS ModExp -- | TODO: module lambda
modExp = only (modBase <|> modApp)
  where
    modBase = ModBase <$> (GModVar . MDCurMod <$> modVar)
    modVar = do
      var <- anyAtom
      ctx <- get
      case fmap isMod $ lookupDecl var ctx of
        Just True -> return var
        _ -> empty
    modApp = empty
  
setExp :: TC SetExp
setExp = setVar -- TODO: add mod deref
  where
    setVar = do
      var <- anyAtom
      ctx <- get
      case fmap isSet $ lookupDecl var ctx of
        Just True -> return $ SetVar var
        _ -> throwError $ var ++ " is not a set in scope."

params :: TCS [Decl Generator]
params = several param

param :: TC (Decl Generator)
param = list . sideeffect (declare . fmap DGGen) $
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
