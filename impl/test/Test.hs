import Data.Foldable

import Control.Applicative
import Control.Monad
import Data.Functor
import Data.List (intercalate)
import Text.Parsec (parse)

import Grammar
import Parse
import TypeCheck

main :: IO ()
main = do
  for_ parsePairs $ \(syn,tree) ->
    case parse program "test" syn of
      Left e ->
        let msg = intercalate "\n" $
              [ "A program should have parsed, but didn't."
              , "The program is"
              , syn
              , "The error message is"
              , show e
              ] in
        error msg
      Right tree' ->
        unless (tree == tree') $
          let msg = intercalate "\n" $
                [ "Program didn't parse into expected tree:\n" ++ syn
                , "expected: " ++ show tree
                , "got: " ++ show tree'
                ] in
          error msg
  for_ goods $ \p ->
    case typeCheckProg p [] of
      Left err -> error ("Program should have type checked but instead got error: " ++ err)
      Right _ -> return ()
  for_ bads $ \p ->
    case typeCheckProg p [] of
      Right _ -> error ("Program should have errored, but type checked: " ++ show p)
      Left err -> return ()
  putStrLn "all tests passed"
  where
    parsePairs = [ (setSyn, [ TLSig set ])
                 , (setsSyn, [TLSig set, TLSig sets])
                 , (badSetsSyn, [TLSig set, TLSig badSets ])
                 , (functionSyn, [TLSig function])
                 , (fun2Syn, [TLSig fun2])
                 , (badfunSyn, [TLSig badfun])
                 , (extfunSyn, [TLSig extfun])
                 , (badextfunSyn, [ TLSig badextfun ])
                 , (tricky_modSyn, tricky_mod)
                 , (fun_comp_ex, fun_comp_tree)
                 ]

-- | for running individual tests in the repl
testProg p = putStrLn $ case typeCheckProg p [] of
  Left err -> err
  Right () -> "Program is well formed"

testParse syn = parse program "" syn

-- | Examples
setSyn :: String
setSyn = intercalate "\n" $
  [ "signature Set() where"
  , "  set X"
  , "end"
  ]

set :: SigDef
set = SigDef "Set" $ SigLam
  { _sigLamArgs = []
  , _sigBody =
    [ SigDeclSet "X"
    ]
  }

setsSyn = ((setSyn ++ "\n\n") ++) $ intercalate "\n" $
  [ "signature Sets() where"
  , "  set X;"
  , "  set Y;"
  , "  set Z"
  , "end"
  ]

sets :: SigDef
sets = SigDef "Sets" $ SigLam
  { _sigLamArgs = []
  , _sigBody =
    [ SigDeclSet "X"
    , SigDeclSet "Y"
    , SigDeclSet "Z"
    ]
  }

badSetsSyn = ((setSyn ++ "\n\n") ++) $ intercalate "\n" $
  [ "signature Sets() where"
  , "  set X;"
  , "  set Y;"
  , "  set X"
  , "end"
  ]

badSets = SigDef "Sets" $ SigLam
  { _sigLamArgs = []
  , _sigBody =
    [ SigDeclSet "X"
    , SigDeclSet "Y"
    , SigDeclSet "X"
    ]
  }




functionSyn = intercalate "\n" $
  [ "signature Fun() where"
  , "  set X;"
  , "  set Y;"
  , "  fun f : X -> Y"
  , "end"
  ]
function :: SigDef
function = SigDef "Fun" $ SigLam
  { _sigLamArgs = []
  , _sigBody =
    [ SigDeclSet "X"
    , SigDeclSet "Y"
    , SigDeclFun "f" (FunType (SetExp (ModDeref Nothing "X")) (SetExp (ModDeref Nothing "Y")))
    ]
  }

fun2Syn = intercalate "\n" $
  [ "signature Fun() where"
  , "  set X;"
  , "  fun f : X -> X;"
  , "  set Y"
  , "end"
  ]

fun2 = SigDef "Fun" $ SigLam
  { _sigLamArgs = []
  , _sigBody =
    [ SigDeclSet "X"
    , SigDeclFun "f" (FunType (SetExp (ModDeref Nothing "X")) (SetExp (ModDeref Nothing "X")))
    , SigDeclSet "Y"
    ]
  }

badfunSyn = intercalate "\n" $
  [ "signature Fun() where"
  , "  set X;"
  , "  fun f : X -> Y"
  , "end"
  ]
badfun = SigDef "Fun" $ SigLam
  { _sigLamArgs = []
  , _sigBody =
    [ SigDeclSet "X"
    , SigDeclFun "f" (FunType (SetExp (ModDeref Nothing "X")) (SetExp (ModDeref Nothing "Y")))
    ]
  }

extfunSyn = intercalate "\n" $
  [ "signature Endo(A: Set()) where"
  , "  fun f : A.X -> A.X"
  , "end"
  ]
extfun = SigDef "Endo" $ SigLam
  { _sigLamArgs = [ ("A", seapp "Set" [])]
  , _sigBody =
    [ SigDeclFun "f" (FunType (SetExp (ModDeref (Just (ModBase "A")) "X")) (SetExp (ModDeref (Just (ModBase "A")) "X")))
    ]
  }

badextfunSyn = intercalate "\n" $
  [ "signature Endo(A: Set()) where"
  , "  fun f : A.Y -> A.Y"
  , "end"
  ]
badextfun = SigDef "Endo" $ SigLam
  { _sigLamArgs = [ ("A", seapp "Set" [])]
  , _sigBody =
    [ SigDeclFun "f" (FunType (SetExp (ModDeref (Just (ModBase "A")) "Y")) (SetExp (ModDeref (Just (ModBase "A")) "Y")))
    ]
  }

tricky_modSyn = intercalate "\n" $
  [ setSyn
  , "signature Weird-Endo(A : Set()) where"
  , "  set X;"
  , "  fun e : A.X -> A.X"
  , "end"
  , ""
  , "module E1(A : Set()) : Weird-Endo(A) where"
  , "  set X = A.X;"
  , "  fun e(x) = x"
  , "end"
  , ""
  -- , "module E2(A : Set, E : Weird-Endo(E1(A).X)) : Weird-Endo(A) where"
  -- , "  set X = A.X;"
  -- , "  fun e(x) = E1(A).e(x)"
  -- , "end"
  ]
tricky_mod =
  [ TLSig $ set
  , TLSig $ SigDef "Weird-Endo" $ SigLam
    { _sigLamArgs = [("A", seapp "Set" [])]
    , _sigBody =
      [ SigDeclSet "X"
      , SigDeclFun "e" (FunType (SetExp (ModDeref (Just $ ModBase "A") "X"))
                                (SetExp (ModDeref (Just $ ModBase "A") "X")))
      ]
    }
  , TLMod $ ModDef
    { _modDefName = "E1"
    , _modDefArgs = [("A", seapp "Set" [])]
    , _modDefSig  = seapp "Weird-Endo" [ ModBase "A" ]
    , _modDefBody =
      [ ModDeclSet "X" (SetExp (ModDeref (Just $ ModBase "A") "X"))
      , ModDeclFun "e" "x" (EEVar "x")
      ]
    }
  ]

fun_comp_ex = intercalate "\n" $
  [ setSyn
  , "signature Function(A : Set(), B : Set()) where"
  , "  fun f : A.X -> B.X"
  , "end"
  , "module Id(A : Set()) : Function(A, A) where"
  , "  fun f(x) = x"
  , "end"
  , "module Comp(A : Set(), B : Set(), C:Set(), F: Function(A,B), G :Function(B,C)) : Function(A,C) where"
  , "  fun f(a) = G.f(F.f(a))"
  , "end"
  ]

fun_comp_tree =
  [ TLSig $ set
  , TLSig $ SigDef "Function" $ SigLam
    { _sigLamArgs = [("A", seapp "Set" []), ("B", seapp "Set" [])]
    , _sigBody =
      [ SigDeclFun "f" (FunType (SetExp (ModDeref (Just $ ModBase "A") "X"))
                                (SetExp (ModDeref (Just $ ModBase "B") "X")))
      ]
    }
  , TLMod $ ModDef
    { _modDefName = "Id"
    , _modDefArgs = [("A", seapp "Set" [])]
    , _modDefSig  = seapp "Function" [ ModBase "A" , ModBase "A"]
    , _modDefBody =
      [ ModDeclFun "f" "x" (EEVar "x")
      ]
    }
  , TLMod $ ModDef
    { _modDefName = "Comp"
    , _modDefArgs = [("A", seapp "Set" []),("B", seapp "Set" []),("C", seapp "Set" []), ("F", seapp "Function" [ModBase "A", ModBase "B"]), ("G", seapp "Function" [ModBase "B", ModBase "C"])]
    , _modDefSig  = seapp "Function" [ ModBase "A" , ModBase "C"]
    , _modDefBody =
      [ ModDeclFun "f" "a" (EEApp (ModDeref (Just $ ModBase "G") "f") . EEApp (ModDeref (Just $ ModBase "F") "f") $ EEVar "a")
      ]
    }
  ]

category :: SigDef
category =
  SigDef "Category" $ SigLam
  { _sigLamArgs = [ ]
  , _sigBody =
    [ SigDeclSet "Ob"
    -- , SigDeclSpan "Arr" (SetExp (ModDeref (ModBase "Category") "Ob")) (SetExp (ModDeref (ModBase "Category") "Ob"))
    -- , SigDeclTerm "id" (TermFunType "forall a. Arr(a,a)")
    -- , SigDeclTerm "comp" (TermFunType "forall a,b,c. (Arr(a,b), Arr(b,c)) -> Arr(a,c)")
    -- , SigDeclAx   "id-left" (TermFunType "forall a,b. (Arr(a,b)) -> Arr(a,b)") TermExp TermExp
    -- | TODO: id-right, assoc
    ]
  }

fctor :: SigDef
fctor =
  SigDef "Functor" $ SigLam
  { _sigLamArgs = [ ("C", seapp "Category" [])
                  , ("D", seapp "Category" [])
                  ]
  , _sigBody = []
  }

-- | Error: C undefined
bad_trans :: SigDef
bad_trans =
  SigDef "Bad Trans" $ SigLam
  { _sigLamArgs = [ ("F", seapp "Functor" [ModBase "C", ModBase "D"])]
  , _sigBody = []
  }
badTrans2 :: SigDef
badTrans2 =
  SigDef "Bad Trans" $ SigLam
  { _sigLamArgs = [ ("F", seapp "Functor" [])]
  , _sigBody = []
  }
badTrans3 :: SigDef
badTrans3 =
  SigDef "Bad Trans" $ SigLam
  { _sigLamArgs = [ ("F", seapp "Functor" [ModBase "F", ModBase "F"])]
  , _sigBody = []
  }

badTrans4 :: SigDef
badTrans4 =
  SigDef "Bad Trans" $ SigLam
  { _sigLamArgs = [ ("A", seapp "Category" [])
                  , ("B", seapp "Category" [])
                  , ("F", seapp "Functor"  [ModBase "A", ModBase "B"])
                  , ("G", seapp "Functor" [ModBase "F", ModBase "F"])
                  ]
  , _sigBody = []
  }
  

trans :: SigDef
trans =
  SigDef "Natural-Transformation" $ SigLam
  { _sigLamArgs = [ ("A", seapp "Category" [])
                  , ("B", seapp "Category" [])
                  , ("F", seapp "Functor"  [ModBase "A", ModBase "B"])
                  , ("G", seapp "Functor"  [ModBase "A", ModBase "B"])
                  ]
  , _sigBody = []
  }

weird :: SigDef
weird =
  SigDef "2-Cell" $ SigLam
  { _sigLamArgs = [ ("A", seapp "Category" [])
                  , ("B", seapp "Category" [])
                  , ("C", seapp "Category" [])
                  , ("F", seapp "Functor"  [ModBase "A", ModBase "B"])
                  , ("G", seapp "Functor"  [ModBase "B", ModBase "C"])
                  , ("alpha", seapp "Natural-Transformation" [ModBase "A", ModBase "B", ModBase "F", ModBase "G"])
                  ]
  , _sigBody = []
  }

simpProg sig = [ TLSig sig ]

good1 = [ TLSig category ]
good2 = good1 ++ [ TLSig fctor ]
good3 = good2 ++ [ TLSig trans ]
goodset = map TLSig [ set, sets ]
goodfun = map TLSig [ function, fun2 ]
goodextfun = goodset ++ simpProg extfun
goods = [ good1, good2, good3, goodset, goodfun , goodextfun ]

bad1 = good2 ++ [ TLSig bad_trans ]
bad2 = good2 ++ [ TLSig badTrans2 ]
bad3 = good2 ++ [ TLSig badTrans3 ]
bad4 = good2 ++ [ TLSig badTrans4 ]
bad5 = good3 ++ [ TLSig weird ]
badfunprog = [TLSig badfun ]
badset = [TLSig badSets ]
badextfunprog = goodset ++ simpProg badextfun
bads = [ bad1, bad2, bad3, bad4, bad5, badset, badextfunprog ]

