module TypeCheck where

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

testProg p = case typeCheckProg p [] of
  Left err -> print err
  Right () -> print "Program is well formed"

typeCheckProg :: Program -> CheckingEnv -> Either String ()
typeCheckProg [] _env = return ()
typeCheckProg (TLSig sigDef : rest) env = do
  typeCheckSigDef sigDef env
  typeCheckProg rest (KnownSig sigDef : env)
typeCheckProg (TLMod modDef : rest) env = modules_unimplemented
  -- typeCheckModDef modDef env
  -- typeCheckProg rest (KnownMod modDef : env)

typeCheckSigDef :: SigDef -> CheckingEnv -> Either String ()
typeCheckSigDef (SigDef sigDefName sigDefArgs sigDefBody) env = do
  typeCheckSigArgs sigDefArgs env
  for_ sigDefBody $ \decl -> 
    typeCheckSigBody decl (addArgs sigDefArgs env)

-- | TODO
typeCheckSigArgs :: [(ModName, SigExp)] -> CheckingEnv -> Either String ()
typeCheckSigArgs args env = case args of
  [] -> return ()
  (name, sig):args -> do
    typeCheckSigExp sig env
    typeCheckSigArgs args (addArgs [(name, sig)] env)

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
typeCheckSigBody :: SigDecl -> CheckingEnv -> Either String ()
typeCheckSigBody = undefined

typeCheckModDef :: ModDef -> CheckingEnv -> Either String ()
typeCheckModDef mod env = modules_unimplemented

addArgs :: [(ModName, SigExp)] -> CheckingEnv -> CheckingEnv
addArgs sigDefArgs env = map (uncurry UnknownMod) sigDefArgs ++ env

lookupSig :: SigName -> CheckingEnv -> Either String SigDef
lookupSig name = find_else matchingSig ("undefined signature: " ++ name)
  where
    matchingSig (KnownSig sigDef) | name == (_sigDefName sigDef) = Just sigDef
    matchingSig _ = Nothing

lookupMod :: ModName -> CheckingEnv -> Either String SigExp
lookupMod name = find_else matchingMod ("undefined module: " ++ name)
  where
    matchingMod (UnknownMod name' sig) | name == name' = Just sig
    matchingMod _ = Nothing

find_else :: (a -> Maybe b) -> e -> [a] -> Either e b
find_else f err = maybe (Left err) Right . getFirst . foldMap (First . f)

modules_unimplemented :: Either String a
modules_unimplemented = Left "Modules are not yet implemented"

typeError :: String -> Either String a
typeError = Left

success :: Either String ()
success = Right ()
