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
typeCheckTL (TLMod (ModDef name lam)) = typeCheckModLam lam

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
          (sigName, sigDecls) <- normalizeSigExp sig prevArgs
          loop args ((name, SigApp (SELam sigName (SigLam [] sigDecls)) []) : prevArgs)

normalizeSigExp :: SigExp -> CheckingEnv -> TC (SigName, [SigDecl])
normalizeSigExp (SigApp sigCtor args) env = case sigCtor of
  SEName name -> typeError $ "undefined signature " ++ name
  SELam name (SigLam params body)  -> do
    let sig_len = length params
        mod_len = length args
    when (sig_len /= mod_len) $
      typeError ("signature " ++ name ++ " expected " ++ show sig_len ++ " args, but got " ++ show mod_len ++ ".")
    newBod <- betaSigApp name (zip params args) body env
    return (name, newBod)

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

typeCheckSigBody :: [SigDecl] -> CheckingEnv -> TC ()
typeCheckSigBody decls env = loop decls []
  where
    loop [] prev           = return ()
    loop (decl:decls) prev =
      let name = declName decl in
        do notDupName name prev
           typeCheckSigDecl decl prev env
           loop decls (decl:prev)

typeCheckSigDecl :: SigDecl -> [SigDecl] -> CheckingEnv -> Either String ()
typeCheckSigDecl decl resolvedDecls env = case decl of
  SigDeclSet  set -> return ()
  SigDeclFun  funName (FunType dom cod) -> do
    typeCheckSetExp dom resolvedDecls env
    typeCheckSetExp cod resolvedDecls env
  SigDeclSpan spanName covar contra     -> do
    typeCheckSetExp covar resolvedDecls env
    typeCheckSetExp contra resolvedDecls env
  SigDeclTerm termName termType         -> typeError "no terms yet"
  SigDeclAx   axName termType t1 t2     -> typeError "axioms are not yet supported"

typeCheckSetExp :: SetExp -> [SigDecl] -> CheckingEnv -> TC ()
typeCheckSetExp (SetExp mderef) resolved env = do
  decl <- lookupFld mderef resolved env
  case decl of
    SigDeclSet _ -> return ()
    _ -> typeError $ "got " ++ show decl ++ " where a set was expected"

notDupName :: String -> [SigDecl] -> Either String ()
notDupName name decls = case find ((name ==) . declName) decls of
  Nothing   -> return ()
  Just decl -> typeError $ "duplicate name: " ++ name

typeCheckModLam :: ModLambda -> TC ()
typeCheckModLam (ModLam params osig bod) = do
  typeCheckSigArgs params
  (osigName, osigDecls) <- normalizeSigExp osig params
  typeCheckModBody bod osigName osigDecls params

-- todo: get the module name over here
typeCheckModBody :: [ModDecl] -> SigName -> [SigDecl] -> CheckingEnv -> Either String ()
typeCheckModBody mdecls signame sigdecls env = case (mdecls, sigdecls) of
  ([],[]) -> return ()
  (mdecl:_,[]) -> typeError $ "Module has field " ++ show mdecl ++ " that is not in signature " ++ signame
  ([],sigdecl:_) -> typeError $ "Module is missing field " ++ show sigdecl ++ " from signature " ++ signame
  (mdecl:mdecls, sigdecl:sigdecls) -> do
    when (mdeclName mdecl /= declName sigdecl) $ misAligned mdecl sigdecl
    case (mdecl, sigdecl) of
      (ModDeclSet _ setExp, SigDeclSet _) -> return ()
      (ModDeclFun fname var eltExp, SigDeclFun fname' (FunType dom cod)) -> do
        typeCheckSetExp dom sigdecls env
        typeCheckSetExp cod sigdecls env
        typeCheckEltExp var dom eltExp cod sigdecls env
      (ModDeclSpan _ _ _ _, SigDeclSpan _ _ _) -> typeError "no spans yet"
      (ModDeclTerm _ _ _ _ _, SigDeclTerm _ _) -> typeError "no terms yet"
      (ModDeclProof _ _, SigDeclAx _ _ _ _)-> typeError "no proofs yet"
      (mdecl, sigdecl) -> misAligned mdecl sigdecl
    typeCheckModBody mdecls signame sigdecls env
  where misAligned mdecl sigdecl = typeError $ "module and signature names don't align, expected a  " ++ show sigdecl ++ " but got a " ++ show mdecl

typeCheckEltExp :: EltVar
             -> SetExp
             -> EltExp
             -> SetExp
             -> [SigDecl]
             -> CheckingEnv
             -> TC ()
typeCheckEltExp var varType e oType sdecls env = do
  infType <- typeInferEltExp var varType e sdecls env
  when (infType /= oType) $
    typeError $ "element expression " ++ show e ++ "has type" ++ show infType ++ " but should have type" ++ show oType

typeInferEltExp :: EltVar
             -> SetExp
             -> EltExp
             -> [SigDecl]
             -> CheckingEnv
             -> TC SetExp
typeInferEltExp var varType e sdecls env = case e of
  EEVar var' -> do
    when (var /= var') $
      typeError $ "unbound variable " ++ var'
    return varType
  EEApp fun earg -> do
    infcod <- typeInferEltExp var varType earg sdecls env
    (FunType fdom fcod) <- lookupFun fun sdecls env
    when (fdom /= infcod) $
      typeError $ "function " ++ show fun ++ " expects a " ++ show fdom ++ " input, but was applied to expression " ++ show earg ++ " which has type " ++ show infcod
    return fcod

lookupFld :: ModDeref String -> [SigDecl] -> CheckingEnv -> TC SigDecl
lookupFld (ModDeref mod fld) sdecls env = case mod of
  Just (ModBase (Bound modName)) -> do
    (SigApp ctor args) <- lookupMod modName env
    case ctor of
      SEName unBoundSig -> typeError $ "THIS IS A BUGGGGGGG"
      SELam name lam -> findFld (_sigBody lam)
  Nothing -> findFld sdecls
  where
    findFld resolved = case getFirst $ foldMap keepIfSame resolved of
      Just decl -> return decl
      Nothing -> typeError $ "undefined field " ++ fld
    
    keepIfSame :: SigDecl -> First SigDecl
    keepIfSame decl | fld == (declName decl) = First . Just $ decl
    keepIfSame _ = First Nothing

lookupFun :: ModDeref FunName -> [SigDecl] -> CheckingEnv -> TC FunType
lookupFun mderef sdecls env = do
  decl <- lookupFld mderef sdecls env
  case decl of
    SigDeclFun _ typ -> return typ
    _ -> typeError $ "got a " ++ show decl ++ " where a fun was expected"

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
