module TypeCheck where

import Control.Monad
import Control.Monad.Identity
import Data.Monoid
import Data.Foldable
import Data.Traversable
import Grammar


type TC a = Either String a

typeCheckProg :: Program -> TC ()
typeCheckProg (Program []) = return ()
typeCheckProg (Program (tl : rest)) = do
  typeCheckTL tl
  typeCheckProg (subst tl (Program rest))

typeCheckTL :: TopLevel -> TC ()
typeCheckTL (TLSig (SigDef name lam)) = typeCheckSigLam lam

-- typeCheckProg (TLMod modDef : rest) env = do
--   typeCheckModDef modDef env
--   typeCheckProg rest env -- TODO: fix, should save

typeCheckSigLam :: SigLambda -> TC ()
typeCheckSigLam (SigLam sigDefArgs sigDefBody) = do
  typeCheckSigArgs sigDefArgs
  typeCheckSigBody sigDefBody sigDefArgs

typeCheckSigArgs :: [(ModName, SigExp)] -> TC ()
typeCheckSigArgs args = loop args []
  where
    loop args prevArgs =
      case args of
        [] -> return ()
        (name, sig):args -> do
          when (elem name (map fst prevArgs)) $
            typeError $ "duplicate name in arguments: " ++ name
          sig' <- normalizeSigExp sig prevArgs
          loop args ((name, sig') : prevArgs)

normalizeSigExp :: SigExp -> CheckingEnv -> TC SigExp
normalizeSigExp (SigApp sigCtor args) env = case sigCtor of
  SEName name -> typeError $ "undefined signature " ++ name
  SELam name (SigLam params body)  -> do
    let sig_len = length params
        mod_len = length args
    when (sig_len /= mod_len) $
      typeError ("signature " ++ name ++ " expected " ++ show sig_len ++ " args, but got " ++ show mod_len ++ ".")
    newBod <- betaSigApp name (zip params args) body env
    return $ SigApp (SELam name (SigLam [] newBod)) []

-- Substitute all of the arguments into the declarations.
-- Precondition is that the sigDecls are already well-typed with respect to the parameters
-- The ModExps are not necessarily well-typed, need to check
betaSigApp :: String -> [((ModName, SigExp), ModExp)] -> [SigDecl] -> CheckingEnv -> Either String [SigDecl]
betaSigApp sigName args bod env = loop args bod
  where
    loop args bod = case args of
      [] -> return bod
      ((argName, sig), mod):args -> do
        typeCheckModArg sigName argName mod sig env
        let newBod = map (substModArg argName mod) bod
        loop args newBod

-- | check if mod satisfies signature sig under environment env
-- | in the context of mod being an argument argName to a signature sigName
typeCheckModArg :: SigName -> ModName -> ModExp -> SigExp -> CheckingEnv -> TC ()
typeCheckModArg sigName argName mod sig env = case mod of
  ModBase (Bound modName) -> do
    msig <- lookupMod modName env
    when (msig /= sig) $
      typeError $ "Module " ++ modName ++ " used as argument " ++ argName ++ " of " ++ sigName ++ " should have signature " ++ show sig ++ " but instead has signature " ++ show msig

substModArg :: ModName -> ModExp -> SigDecl -> SigDecl
substModArg name exp = runIdentity . sigDeclModDerefs (Identity . plug)
  where
    plug :: ModDeref String -> ModDeref String
    plug (ModDeref maymod fld) = case maymod of
      Nothing -> ModDeref Nothing fld
      Just (ModBase name') ->
        let exp' = if name == unbound name'
                   then exp
                   else ModBase name'
        in
          ModDeref (Just exp') fld

typeCheckSigBody sigDefBody sigDefArgs = return ()

-- typeCheckSigExp :: SigExp -> CheckingEnv -> Either String ()
-- typeCheckSigExp (SEApp (SigApp ctor mod_args)) env = do
--   (SigLam sig_args _bod) <- lookupSig ctor env
--   let sig_len = length sig_args
--       mod_len = length mod_args
--   if sig_len /= mod_len
--     then typeError ("constructor " ++ ctor ++ " expected " ++ show sig_len ++ " args, but got " ++ show mod_len ++ ".")
--     else typeCheckModArgs (zip mod_args (map snd sig_args)) env
-- typeCheckSigExp (SELam sigLam) env = typeCheckSigLam sigLam env

-- resolveSigExp :: SigExp -> CheckingEnv -> Either String (CheckingEnv, [SigDecl])
-- resolveSigExp (SELam sigLam) env = do
--   typeCheckSigLam sigLam env
--   return $ ([], _sigBody sigLam)
-- resolveSigExp (SEApp (SigApp ctor mod_args)) env = do
--   (SigLam sig_args bod) <- lookupSig ctor env
--   let sig_len = length sig_args
--       mod_len = length mod_args
--   unless (sig_len == mod_len) $
--     typeError ("constructor " ++ ctor ++ " expected " ++ show sig_len ++ " args, but got " ++ show mod_len ++ ".")
--   typeCheckModArgs (zip mod_args (map snd sig_args)) env
--   return (_, bod)

-- typeCheckModArgs :: [(ModExp, SigExp)] -> CheckingEnv -> Either String ()
-- typeCheckModArgs args env = case args of
--   [] -> success
--   (ModBase modName, sig):args -> do
--     modSig <- lookupMod modName env
--     if modSig == sig
--       then typeCheckModArgs args env
--       else typeError (modName ++ " has signature " ++ show modSig ++ " but was used where a " ++ show sig ++ " is expected")
  
-- -- | TODO
-- typeCheckSigDecl :: SigDecl -> [SigDecl] -> CheckingEnv -> Either String ()
-- typeCheckSigDecl decl resolvedDecls env = case decl of
--   SigDeclSet  set -> do
--     notDupName set resolvedDecls
--   SigDeclFun  funName (FunType dom cod) -> do
--     notDupName funName resolvedDecls
--     typeCheckSetExp dom resolvedDecls env
--     typeCheckSetExp cod resolvedDecls env
--   SigDeclSpan spanName covar contra     -> do
--     notDupName spanName resolvedDecls
--     typeCheckSetExp covar resolvedDecls env
--     typeCheckSetExp contra resolvedDecls env
--   SigDeclTerm termName termType         -> typeError "no terms yet"
--   SigDeclAx   axName termType t1 t2     -> typeError "axioms are not yet supported"

-- typeCheckSigBody :: [SigDecl] -> CheckingEnv -> Either String ()
-- typeCheckSigBody decls env = loop decls [] env
--   where
--     loop [] resolvedDecls env = return ()
--     loop (decl:decls) resolvedDecls env = do
--       typeCheckSigDecl decl resolvedDecls env
--       loop decls (decl:resolvedDecls) env

-- typeCheckSetExp :: SetExp -> [SigDecl] -> CheckingEnv -> Either String ()
-- typeCheckSetExp (SetExp (ModDeref mayMod setName)) resolved env = case mayMod of
--   Just (ModBase modName) -> do
--     (SEApp (SigApp ctor _)) <- lookupMod modName env
--     sig             <- lookupSig ctor env
--     findSet (_sigBody sig)
--   Nothing -> findSet resolved
--   where
--     findSet resolved = case getFirst $ foldMap keepIfSame resolved of
--       Just (SigDeclSet _) -> return ()
--       Just decl' -> typeError $ "got " ++ show decl' ++ " where a set was expected"
--       Nothing -> typeError $ "undefined set " ++ setName
    
--     keepIfSame :: SigDecl -> First SigDecl
--     keepIfSame decl | setName == (getName decl) = First . Just $ decl
--     keepIfSame _ = First Nothing

-- notDupName :: String -> [SigDecl] -> Either String ()
-- notDupName name decls = case find ((name ==) . getName) decls of
--   Nothing   -> return ()
--   Just decl -> typeError $ "duplicate name: " ++ name

-- typeCheckModDef :: ModDef -> CheckingEnv -> Either String ()
-- typeCheckModDef (ModDef _name args osig bod) env = do
--   typeCheckSigArgs args env
--   let arg_env = addArgs args env
--   sigdecls <- resolveSigExp osig arg_env
--   typeCheckModBody bod sigdecls arg_env

-- -- Strategy: 
-- typeCheckModBody :: [ModDecl] -> [SigDecl] -> CheckingEnv -> Either String ()
-- typeCheckModBody decls sigdecls env = undefined

-- addArgs :: [(ModName, SigExp)] -> CheckingEnv -> CheckingEnv
-- addArgs sigDefArgs env = map (uncurry UnknownMod) sigDefArgs ++ env

-- lookupSig :: SigName -> CheckingEnv -> Either String SigLambda
-- lookupSig name = find_else matchingSig ("undefined signature: " ++ name)
--   where
--     matchingSig (KnownSig sigDef) =
--       if name == (_sigDefName sigDef)
--       then Just (_sigLambda sigDef)
--       else Nothing
--     -- matchingSig (KnownMod _) = Nothing
--     matchingSig (UnknownMod _ _)  = Nothing

lookupMod :: ModName -> CheckingEnv -> Either String SigExp
lookupMod name = find_else matchingMod ("undefined module: " ++ name)
  where
    matchingMod (name', sig) = if name == name' then Just sig else Nothing

find_else :: (a -> Maybe b) -> e -> [a] -> Either e b
find_else f err = maybe (Left err) Right . getFirst . foldMap (First . f)

modules_unimplemented :: Either String a
modules_unimplemented = Left "Modules are not yet implemented"

typeError :: String -> Either String a
typeError = Left

success :: Either String ()
success = Right ()
