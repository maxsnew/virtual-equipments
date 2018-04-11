import Data.Foldable

import Grammar
import TypeCheck

main :: IO ()
main = do
  for_ goods $ \p ->
    case typeCheckProg p [] of
      Left err -> error ("Program should have type checked but instead got error: " ++ err)
      Right _ -> return ()
  for_ bads $ \p ->
    case typeCheckProg p [] of
      Right _ -> error ("Program should have errored, but type checked: " ++ show p)
      Left err -> return ()
  putStrLn "all tests passed"

-- | for running individual tests in the repl
testProg p = putStrLn $ case typeCheckProg p [] of
  Left err -> err
  Right () -> "Program is well formed"

-- | Examples
set :: SigDef
set = SigDef
  { _sigDefName = "Set"
  , _sigDefArgs = []
  , _sigDefBody =
    [ SigDeclSet "X"
    ]
  }

sets :: SigDef
sets = SigDef
  { _sigDefName = "Sets"
  , _sigDefArgs = []
  , _sigDefBody =
    [ SigDeclSet "X"
    , SigDeclSet "Y"
    , SigDeclSet "Z"
    ]
  }

badSets = SigDef
  { _sigDefName = "Sets"
  , _sigDefArgs = []
  , _sigDefBody =
    [ SigDeclSet "X"
    , SigDeclSet "Y"
    , SigDeclSet "X"
    ]
  }

function :: SigDef
function = SigDef
  { _sigDefName = "Fun"
  , _sigDefArgs = []
  , _sigDefBody =
    [ SigDeclSet "X"
    , SigDeclSet "Y"
    , SigDeclFun "f" (FunType (SetExp (ModDeref Nothing "X")) (SetExp (ModDeref Nothing "Y")))
    ]
  }

fun2 = SigDef
  { _sigDefName = "Fun"
  , _sigDefArgs = []
  , _sigDefBody =
    [ SigDeclSet "X"
    , SigDeclFun "f" (FunType (SetExp (ModDeref Nothing "X")) (SetExp (ModDeref Nothing "X")))
    , SigDeclSet "Y"
    ]
  }

badfun = SigDef
  { _sigDefName = "Fun"
  , _sigDefArgs = []
  , _sigDefBody =
    [ SigDeclSet "X"
    , SigDeclFun "f" (FunType (SetExp (ModDeref Nothing "X")) (SetExp (ModDeref Nothing "Y")))
    ]
  }

extfun = SigDef
  { _sigDefName = "Endo"
  , _sigDefArgs = [ ("A", SigApp "Set" [])]
  , _sigDefBody =
    [ SigDeclFun "f" (FunType (SetExp (ModDeref (Just (ModBase "A")) "X")) (SetExp (ModDeref (Just (ModBase "A")) "X")))
    ]
  }

badextfun = SigDef
  { _sigDefName = "Endo"
  , _sigDefArgs = [ ("A", SigApp "Set" [])]
  , _sigDefBody =
    [ SigDeclFun "f" (FunType (SetExp (ModDeref (Just (ModBase "A")) "Y")) (SetExp (ModDeref (Just (ModBase "A")) "Y")))
    ]
  }

category :: SigDef
category =
  SigDef
  { _sigDefName = "Category"
  , _sigDefArgs = [ ]
  , _sigDefBody =
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
  SigDef
  { _sigDefName = "Functor"
  , _sigDefArgs = [ ("C", SigApp "Category" [])
                  , ("D", SigApp "Category" [])
                  ]
  , _sigDefBody = []
  }

-- | Error: C undefined
bad_trans :: SigDef
bad_trans =
  SigDef
  { _sigDefName = "Bad Trans"
  , _sigDefArgs = [ ("F", SigApp "Functor" [ModBase "C", ModBase "D"])]
  , _sigDefBody = []
  }
badTrans2 :: SigDef
badTrans2 =
  SigDef
  { _sigDefName = "Bad Trans"
  , _sigDefArgs = [ ("F", SigApp "Functor" [])]
  , _sigDefBody = []
  }
badTrans3 :: SigDef
badTrans3 =
  SigDef
  { _sigDefName = "Bad Trans"
  , _sigDefArgs = [ ("F", SigApp "Functor" [ModBase "F", ModBase "F"])]
  , _sigDefBody = []
  }

badTrans4 :: SigDef
badTrans4 =
  SigDef
  { _sigDefName = "Bad Trans"
  , _sigDefArgs = [ ("A", SigApp "Category" [])
                  , ("B", SigApp "Category" [])
                  , ("F", SigApp "Functor"  [ModBase "A", ModBase "B"])
                  , ("G", SigApp "Functor" [ModBase "F", ModBase "F"])
                  ]
  , _sigDefBody = []
  }
  

trans :: SigDef
trans =
  SigDef
  { _sigDefName = "Natural-Transformation"
  , _sigDefArgs = [ ("A", SigApp "Category" [])
                  , ("B", SigApp "Category" [])
                  , ("F", SigApp "Functor"  [ModBase "A", ModBase "B"])
                  , ("G", SigApp "Functor"  [ModBase "A", ModBase "B"])
                  ]
  , _sigDefBody = []
  }

weird :: SigDef
weird =
  SigDef
  { _sigDefName = "2-Cell"
  , _sigDefArgs = [ ("A", SigApp "Category" [])
                  , ("B", SigApp "Category" [])
                  , ("C", SigApp "Category" [])
                  , ("F", SigApp "Functor"  [ModBase "A", ModBase "B"])
                  , ("G", SigApp "Functor"  [ModBase "B", ModBase "C"])
                  , ("alpha", SigApp "Natural-Transformation" [ModBase "A", ModBase "B", ModBase "F", ModBase "G"])
                  ]
  , _sigDefBody = []
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
