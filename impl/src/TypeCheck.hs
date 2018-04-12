module TypeCheck where

import Control.Monad (when)
import Data.Monoid
import Data.Foldable
import Data.Traversable
import Grammar

-- | These are already type-checked modules, and bindings earlier in
-- the list shadow later ones
type CheckingEnv = [Binding]
data Binding
  = KnownSig SigDef
  -- | KnownMod ModDef -- ^ TODO
  | UnknownMod ModName SigExp

type TC a = CheckingEnv -> Either String a

typeCheckProg :: Program -> CheckingEnv -> Either String ()
typeCheckProg [] _env = return ()
typeCheckProg (TLSig sigDef : rest) env = do
  typeCheckSigDef sigDef env
  typeCheckProg rest (KnownSig sigDef : env)
typeCheckProg (TLMod modDef : rest) env = do
  typeCheckModDef modDef env
  typeCheckProg rest (undefined : env) -- | TODO: fix

typeCheckSigDef :: SigDef -> CheckingEnv -> Either String ()
typeCheckSigDef (SigDef _ sigDefArgs sigDefBody) env = do
  typeCheckSigArgs sigDefArgs env
  typeCheckSigBody sigDefBody (addArgs sigDefArgs env)

typeCheckSigArgs :: [(ModName, SigExp)] -> CheckingEnv -> Either String ()
typeCheckSigArgs args env = loop args [] env
  where
    loop args oldNames env =
      case args of
        [] -> return ()
        (name, sig):args -> do
          when (elem name oldNames) $
            typeError $ "duplicate name in arguments: " ++ name
          typeCheckSigExp sig env
          loop args (name:oldNames) (addArgs [(name, sig)] env)

typeCheckSigExp :: SigExp -> CheckingEnv -> Either String ()
typeCheckSigExp (SigApp ctor mod_args) env = do
  (SigDef _ctor sig_args _bod) <- lookupSig ctor env
  let sig_len = length sig_args
      mod_len = length mod_args
  if sig_len /= mod_len
    then typeError ("constructor " ++ _ctor ++ " expected " ++ show sig_len ++ " args, but got " ++ show mod_len ++ ".")
    else typeCheckModArgs (zip mod_args (map snd sig_args)) env


typeCheckModArgs :: [(ModExp, SigExp)] -> CheckingEnv -> Either String ()
typeCheckModArgs args env = case args of
  [] -> success
  (ModBase modName, sig):args -> do
    modSig <- lookupMod modName env
    if modSig == sig
      then typeCheckModArgs args env
      else typeError (modName ++ " has signature " ++ show modSig ++ " but was used where a " ++ show sig ++ " is expected")
  
-- | TODO
typeCheckSigDecl :: SigDecl -> [SigDecl] -> CheckingEnv -> Either String ()
typeCheckSigDecl decl resolvedDecls env = case decl of
  SigDeclSet  set -> do
    notDupName set resolvedDecls
  SigDeclFun  funName (FunType dom cod) -> do
    notDupName funName resolvedDecls
    typeCheckSetExp dom resolvedDecls env
    typeCheckSetExp cod resolvedDecls env
  SigDeclSpan spanName covar contra     -> do
    notDupName spanName resolvedDecls
    typeCheckSetExp covar resolvedDecls env
    typeCheckSetExp contra resolvedDecls env
  SigDeclTerm termName termType         -> typeError "no terms yet"
  SigDeclAx   axName termType t1 t2     -> typeError "axioms are not yet supported"

typeCheckSigBody :: [SigDecl] -> CheckingEnv -> Either String ()
typeCheckSigBody decls env = loop decls [] env
  where
    loop [] resolvedDecls env = return ()
    loop (decl:decls) resolvedDecls env = do
      typeCheckSigDecl decl resolvedDecls env
      loop decls (decl:resolvedDecls) env

typeCheckSetExp :: SetExp -> [SigDecl] -> CheckingEnv -> Either String ()
typeCheckSetExp (SetExp (ModDeref mayMod setName)) resolved env = case mayMod of
  Just (ModBase modName) -> do
    (SigApp ctor _) <- lookupMod modName env
    sig             <- lookupSig ctor env
    findSet (_sigDefBody sig)
  Nothing -> findSet resolved
  where
    findSet resolved = case getFirst $ foldMap keepIfSame resolved of
      Just (SigDeclSet _) -> return ()
      Just decl' -> typeError $ "got " ++ show decl' ++ " where a set was expected"
      Nothing -> typeError $ "undefined set " ++ setName
    
    keepIfSame :: SigDecl -> First SigDecl
    keepIfSame decl | setName == (getName decl) = First . Just $ decl
    keepIfSame _ = First Nothing

notDupName :: String -> [SigDecl] -> Either String ()
notDupName name decls = case find ((name ==) . getName) decls of
  Nothing   -> return ()
  Just decl -> typeError $ "duplicate name: " ++ name

typeCheckModDef :: ModDef -> CheckingEnv -> Either String ()
typeCheckModDef (ModDef _name args osig bod) env = do
  typeCheckSigArgs args env
  let arg_env = addArgs args env
  typeCheckSigExp osig arg_env
  typeCheckModBody bod osig arg_env

-- | 
typeCheckModBody :: [ModDecl] -> SigExp -> CheckingEnv -> Either String ()
typeCheckModBody decls sig env = _

addArgs :: [(ModName, SigExp)] -> CheckingEnv -> CheckingEnv
addArgs sigDefArgs env = map (uncurry UnknownMod) sigDefArgs ++ env

lookupSig :: SigName -> CheckingEnv -> Either String SigDef
lookupSig name = find_else matchingSig ("undefined signature: " ++ name)
  where
    matchingSig (KnownSig sigDef) =
      if name == (_sigDefName sigDef)
      then Just sigDef
      else Nothing
    -- matchingSig (KnownMod _) = Nothing
    matchingSig (UnknownMod _ _)  = Nothing

lookupMod :: ModName -> CheckingEnv -> Either String SigExp
lookupMod name = find_else matchingMod ("undefined module: " ++ name)
  where
    matchingMod (UnknownMod name' sig) = if name == name' then Just sig else Nothing
    -- matchingMod (KnownMod mod) = if name == _modDefName mod then Just (_modDefSig mod) else Nothing
    matchingMod (KnownSig _) = Nothing

find_else :: (a -> Maybe b) -> e -> [a] -> Either e b
find_else f err = maybe (Left err) Right . getFirst . foldMap (First . f)

modules_unimplemented :: Either String a
modules_unimplemented = Left "Modules are not yet implemented"

typeError :: String -> Either String a
typeError = Left

success :: Either String ()
success = Right ()
