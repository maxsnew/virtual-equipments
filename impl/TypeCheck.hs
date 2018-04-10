module TypeCheck where

import Data.Foldable
import Data.Traversable
import Grammar

-- | These are already type-checked modules, in reverse order
type CheckingEnv = [Binding]
data Binding
  = KnownSig SigDef
  | KnownMod ModDef
  | UnkownMod ModName SigExp

type TC a = CheckingEnv -> Either String a

typeCheckProg :: Program -> CheckingEnv -> Either String ()
typeCheckProg ProgMT env = return ()
typeCheckProg (ProgSig sigDef rest) env = do
  typeCheckSigDef sigDef env
  typeCheckProg rest (KnownSig sigDef : env)
typeCheckProg (ProgMod modDef rest) env = do
  typeCheckModDef modDef env
  typeCheckProg rest (KnownMod modDef : env)

typeCheckSigDef :: SigDef -> CheckingEnv -> Either String ()
typeCheckSigDef (SigDef sigDefName sigDefArgs sigDefBody) env = do
  typeCheckSigArgs sigDefArgs env
  for_ sigDefBody $ \decl -> 
    typeCheckSigBody decl (addArgs sigDefArgs env)

-- | TODO
typeCheckSigArgs :: [(ModName, SigExp)] -> CheckingEnv -> Either String ()
typeCheckSigArgs args env = return ()

-- | TODO
typeCheckSigBody :: SigDecl -> CheckingEnv -> Either String ()
typeCheckSigBody = _

addArgs :: [(ModName, SigExp)] -> CheckingEnv -> CheckingEnv
addArgs sigDefArgs env = map (uncurry UnkownMod) sigDefArgs ++ env

typeCheckModDef :: ModDef -> CheckingEnv -> Either String ()
typeCheckModDef mod env = Left "Modules are not yet implemented"
