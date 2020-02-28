import Data.Foldable

import Control.Applicative
import Control.Monad
import Data.Either
import Data.Functor
import Data.List (intercalate)
import Data.Traversable
import Text.Parsec (parse)

import Test.HUnit

import Syntax
import Parse
import TypeCheck

main :: IO ()
main = void $ runTestTT tests
  where tests = test [ parseTests
                     , tcTests
                     ]



tcTests = "Type Checking Tests" ~: test [ goodTests
                                        , badTests
                                        ]
goodTests = "Successful Type Checks" ~: test
  [ assertTC "empty program" ""
  , assertTC "world's smallest module" "(def-mod M (mod ()))"
  , assertTC "sets in params" "(def-mod S (mod ((set X) (set Y)) ))"
  , assertTC "definition of a set" "(def-mod M (mod ((set X)) (def-set Y X)))"
  , assertTC "fun in params"  "(def-mod S (mod ((set X) (fun f X X)) ))"
  , assertTC "more fun in params" "(def-mod S (mod ((set X) (set Y) (fun f Y X)) ))"
  , assertTC "id fun sig" "(def-mod ID (mod ((set X))  ))"
  , assertTC "id fun" "(def-mod ID (mod ((set X))  (def-fun id (x X) X x)))"
  , assertTC "endo-comp" "(def-mod SELFCOMP (mod ((set X) (fun f X X))  (def-fun g (x X) X (f x))))"
  , assertTC "many endo-comp" "(def-mod MANYSELFCOMP (mod ((set X) (fun f X X))  (def-fun g (x X) X (f (f (f (f x)))))))"
  , assertTC "many endo-comp" "(def-mod COMP (mod ((set X) (set Y) (fun f X Y) (set Z) (fun g Y Z))  (def-fun h (x X) Z (g (f x))))))"
  , assertTC "span in params" "(def-mod S (mod ((set X) (set Y) (span R X Y)) ))"
  , assertTC "span in params" "(def-mod S (mod ((set X) (set Y) (span R X X)) ))"
  , assertTC "span eta" "(def-mod S (mod ((set X) (set Y) (fun f X Y) (span R X Y)) (def-span Q (x X) (y Y) (R x y))))"
  , assertTC "span subst" "(def-mod S (mod ((set X) (set Y) (fun f X Y) (span R X Y)) (def-span Q (x X) (x' X) (R x (f x')))))"
  , assertTC "cat id param"
    "(def-mod S (mod ((set Ob) (span Mor Ob Ob) (trans id ((X Ob)) () (Mor X X))) ))"
  , assertTC "cat compose params"
    "(def-mod S (mod ((set Ob) (span Mor Ob Ob) (trans comp ((X Ob) (Y Ob) (Z Ob)) ((Mor X Y) (Mor Y Z)) (Mor X Z))) ))"
  , assertTC "cat data params"
    "(def-mod S (mod ((set Ob) (span Mor Ob Ob) (trans id ((X Ob)) () (Mor X X)) (trans comp ((X Ob) (Y Ob) (Z Ob)) ((Mor X Y) (Mor Y Z)) (Mor X Z)))))"
  , assertTC "RUP"
    "(def-mod S (mod ((set A) (span HomA A A) (set B) (fun G B A) (span M A B) (trans counit ((b B)) () (M (G b) b)) (trans intro ((a A) (b B)) ((M a b)) (HomA a (G b))))))"
  , assertTC "ID-trans-params"
    "(def-mod ID-trans (mod ((set A) (span R A A))  ))"
  -- , assertTC "ID-trans"
  --   "(def-mod ID-trans (mod ((set A) (span R A A))  (def-trans id ((a A) (a' A)) ((x (R a a'))) (R a a') x)))"
  -- , assertTC "trans eta empty"
  --   "(def-mod trans-eta (mod ((set A) (span R A A) (trans foo ((a A)) () (R a a)))  (def-trans bar ((a A)) () (R a a) (foo))))"
  -- , assertTC "trans eta one-arg"
  --   "(def-mod trans-eta (mod ((set A) (set B) (span Q A B) (span R A B) (trans foo ((a A) (b B)) ((Q a b)) (R a b)))  (def-trans bar ((a A) (b B)) ((x (Q a b))) (R a b) (foo x))))"
  -- , assertTC "trans eta inst"
  --   "(def-mod trans-eta (mod ((set A) (set B) (fun F A B) (span R B B) (trans foo ((b B)) () (R b b)))  (def-trans bar ((a A)) () (R (F a) (F a)) (foo))))"
  -- , assertTC "iterate trans"
  --   "(def-mod iter (mod ((set A) (set B) (span R A B) (trans f ((a A) (b B)) ((R a b)) (R a b))) (def-trans fffff ((a A) (b B)) ((x (R a b))) (R a b) (f (f (f (f (f x))))))))"
  , assertTC "define submodule"
  "(def-mod foo (mod ((set X)) (def-mod S (mod () (def-set Y X)))))"
  , assertTC "use submodule"
  "(def-mod foo (mod ((set X)) (def-mod S (mod () (def-set Y X))) (def-set Z (. S Y))))" -- woot!
  ]
--   , typeChecks (Program good2) ~? "functor signature"
--   , typeChecks (Program good3) ~? "transformation signature"
--   , typeChecks (Program goodset) ~? "sets signature"
--   , typeChecks (Program goodfun) ~? "function signature"
--   , typeChecks (Program goodextfun) ~? "module deref in signature"
--   , typeChecks modTest1 ~? "module with identity function"
--   , typeChecks modTest2 ~? "module with supplied function"
--   , typeChecks modTest3 ~? "module with composition of functions"
--   , typeChecks modTest4 ~? "module with big composition of function"
--   , typeChecks spanmod0 ~? "span signatures"
--   , typeChecks spanmod1 ~? "eta expanded span"
--   , typeChecks spanmod2 ~? "span with restriction"
--   , typeChecks spanmod3 ~? "span with more restriction"
--   ]
badTests = "Type Checking Failures" ~: test
  [ not (typeChecks "()") ~? "empty decl"
  , not (typeChecks "(def-mod _ (mod (set X) (set Y)))") ~? "params are parenthesized"
  , not (typeChecks "(def-mod S (mod ((fun f X X)) ))") ~? "set out of scope in fun decl"
  , not (typeChecks "(def-mod S (mod ((set X) (fun f X Y)) ))") ~? "var out of scope"
  -- , not (typeChecks "(def-mod S (((set X) (set Y) (fun f X Y)) (span R X f)))") ~? "more signature"
  , not (typeChecks "(def-mod M (mod ((set X)) (sig ) (def-set Y Y)))") ~? "set out of scope"
  , not (typeChecks "(def-mod M (mod ((set X) (set Y))  (def-fun f (x X) Y x)))") ~? "type error in fun def"
  , not (typeChecks "(def-mod M (mod ((set X) (set Y) (fun f X Y) (fun g X Y))  (def-fun h (x X) Y (g (f x)))))") ~? "type error in fun comp"
  , not (typeChecks "(def-mod ID (mod ((set X) (fun g X X))  (def-fun id (x g) g x)))") ~? "fun used as a set"
  , not (typeChecks "(def-mod ID (mod ((set X))  (def-fun id (x X) X (X x))))") ~? "set used as a fun"
  , not (typeChecks "(def-mod S (mod ((set Ob) (span Mor Ob Ob) (trans comp ((X Ob) (Y Ob)) () (Mor X X))) ))") ~? "cat id too many indices"
  , not (typeChecks "(def-mod S (mod ((set Ob) (span Mor Ob Ob) (trans comp ((X Ob)) ((Mor X X)) (Mor X X))) ))") ~? "cat not enough indices"
  -- , not (typeChecks "(def-mod ID-trans (mod ((set A) (span R A A))  (def-trans id (a A) ((x (R a a))) (R a a) x)))")
  -- ~? "trans indices need to be parenthesized"
  -- , not (typeChecks "(def-mod ID-trans (mod ((set A) (span R A A))  (def-trans id ((a A)) (x (R a a)) (R a a) x)))")
  -- ~? "trans vars need to be parenthesized"
  -- , not (typeChecks "(def-mod ID-trans (mod ((set A) (span R A A))  (def-trans id ((a A)) ((x (R a a))) (R a a) x)))")
  -- ~? "improper duplication of indices"
  -- , not (typeChecks "(def-mod ID-trans (mod ((set A) (span R A A))  (def-trans id ((a A) (a' A)) ((x (R a a))) (R a a') x)))")
  -- ~? "more improper duplication of indices"
  -- , not (typeChecks  
  --   "(def-mod trans-eta (mod ((set A) (set B) (span Q A B) (span R A B) (trans foo ((a A) (b B)) ((Q a b)) (R a b)))  (def-trans bar ((a A) (b B)) ((x (Q a b))) (R a b) (foo))))")
  --   ~? "unused var"
  -- , not (typeChecks  
  --   "(def-mod trans-eta (mod ((set A) (set B) (span Q A B) (span R A B) (trans foo ((a A) (b B)) ((Q a b)) (R a b)))  (def-trans bar ((a A) (b B)) ((x (Q a b))) (R a b) (foo x x))))")
  --   ~? "doubly arity mismatch"
  -- , not (typeChecks
  --   "(def-mod trans-eta (mod ((set A) (set B) (fun F A B) (span R B B) (trans foo ((a A)) () (R (F a) (F a))))  (def-trans bar ((b B)) () (R b b) (foo))))")
  --  ~? "transformations' type is too specific"
-- , not (typeChecks "(def-mod S (() (set X))) (def-sig T (sig () (fun R X X)))") ~? "locality of scope"
--  , not (typeChecks "(def-mod M (mod ((set X)) (sig ) (def-set Y X)))") ~? "module defines too many things?"
  ]
--   [ not (typeChecks (Program bad1)) ~? "C should be undefined"
--   , not (typeChecks (Program bad2)) ~? "Functor given wrong number of arguments"
--   , not (typeChecks (Program bad3)) ~? "Functor applied to unbound arguments"
--   , not (typeChecks (Program bad4)) ~? "Functor applied to non-category arguments"
--   , not (typeChecks (Program bad5)) ~? "G should have type Functor(A,B) but has type Functor(B,C)"
--   , not (typeChecks (Program badset)) ~? "X bound twice in signature"
--   , not (typeChecks (Program badextfunprog)) ~? "Invalid field Y in Set"
--   , not (typeChecks wrongOrder) ~? "module fields defined in wrong order"
--   , not (typeChecks wrongVar) ~? "free variable in element expr"
--   , not (typeChecks badField) ~? "undefined field referenced in module"
--   , not (typeChecks badTypeFun) ~? "ill typed element expr"
--   ]

assertTC errmsg syn =
  assertEqual errmsg
  (Right ())
  (() <$ (typeCheck TypeCheck.program =<< (mapLeft show (parse Parse.program "test" syn))))

typeChecks s = isRight $
  (mapLeft show (parse Parse.program "test" s)) >>=
  typeCheck TypeCheck.program

-- notTypeChecks s = 

mapLeft f = either (Left . f)  Right

-- simpProg sig = [ TLSig sig ]


-- good1 = [ TLSig category ]
-- good2 = good1 ++ [ TLSig fctor ]
-- good3 = good2 ++ [ TLSig trans ]
-- goodset = map TLSig [ set, sets ]
-- goodfun = map TLSig [ function, fun2 ]
-- goodextfun = goodset ++ simpProg extfun
-- goods = map Program [ good1, good2, good3, goodset, goodfun , goodextfun ]

-- bad1 = good2 ++ [ TLSig bad_trans ]
-- bad2 = good2 ++ [ TLSig badTrans2 ]
-- bad3 = good2 ++ [ TLSig badTrans3 ]
-- bad4 = good2 ++ [ TLSig badTrans4 ]
-- bad5 = good3 ++ [ TLSig weird ]
-- badfunprog = [TLSig badfun ]
-- badset = [TLSig badSets ]
-- badextfunprog = goodset ++ simpProg badextfun
-- bads = map Program [ bad1, bad2, bad3, bad4, bad5, badset, badextfunprog
--                    ]

-- -- foo = do
-- --   for_ parsePairs $ \(syn,tree) ->
-- --     case parse program "test" syn of
-- --       Left e ->
-- --         let msg = intercalate "\n" $
-- --               [ "A program should have parsed, but didn't."
-- --               , "The program is"
-- --               , syn
-- --               , "The error message is"
-- --               , show e
-- --               ] in
-- --         error msg
-- --       Right tree' ->
-- --         unless (tree == tree') $
-- --           let msg = intercalate "\n" $
-- --                 [ "Program didn't parse into expected tree:\n" ++ syn
-- --                 , "expected: " ++ show tree
-- --                 , "got: " ++ show tree'
-- --                 ] in
-- --           error msg
-- --   let moreGoods = (`foldMap` shouldParse) $ \should ->
-- --         case parse program "sets module" should of
-- --           Left e -> error $ "This should have parsed\n" ++ should
-- --           Right t -> [t]
-- --   for_ (goods ++ moreGoods) $ \p ->
-- --     case typeCheckProg p of
-- --       Left err -> error ("Program should have type checked but instead got error: " ++ err)
-- --       Right _ -> return ()
-- --   for_ bads $ \p ->
-- --     case typeCheckProg p of
-- --       Right _ -> error ("Program should have errored, but type checked: " ++ show p)
-- --       Left err -> return ()
-- --   putStrLn "all tests passed"
-- --   where
-- --     shouldParse = [intercalate "\n" [setSyn, setsSyn, setsModuleSyn]]

parseTests = "Parsing tests" ~: test
  [ "shouldParse" ~: test
    [ parses "" @? "empty program"
    , parses "()" @? "parens"
    , parses "(def-sig S (sig ()))" @? "sig definition"]
  , "shouldNotParse" ~: test
    [ not (parses "(") @? "unbalanced" ]
  ]
--   [ "shouldParse" ~: test
--     [ parses spanPreamble @? "signatures with spans"
--     , parses simpSpan @? "Eta expand a span"
--     , parses restrictSpan @? "span with restrictions"
--     , parses restrictSpan2 @? "span with bigger restrictions"
--     ]
--   , "parseEqs" ~: test
--   [ "basic signature" ~: (setSyn ~>=? [ TLSig set ])
--   , "multi field sig" ~: (setsSyn ~>=?[TLSig set, TLSig sets])
--   , "multi field sig 2" ~: (badSetsSyn ~>=? [TLSig set, TLSig badSets ])
--   , "function sig" ~: (functionSyn ~>=? [TLSig function])
--   , "fun before set sig" ~: (fun2Syn ~>=? [TLSig fun2])
--   , "fun sig 2" ~: (badfunSyn ~>=? [TLSig badfun])
--   , "deref in sig" ~: (extfunSyn ~>=? [TLSig extfun])
--   , "deref in sig 2" ~: (badextfunSyn ~>=? [ TLSig badextfun ])
--   , "parse mdule " ~: (tricky_modSyn ~>=? tricky_mod)
--   , "module 2" ~: (fun_comp_ex ~>=? fun_comp_tree)
--   ]
--   ]
  where
    parses p = isRight $ parse Parse.program "test" p
--     (~>=?) :: String -> [TopLevel] -> IO Bool
--     syn ~>=? prog = case parse program "test" syn of
--       Left e   -> assertFailure $ show e
--       Right p' -> return $ Program prog == p'

-- -- | for running individual tests in the repl
-- testProg p = putStrLn $ case typeCheckProg p of
--   Left err -> err
--   Right () -> "Program is well formed"

-- testParse syn = parse program "" syn

-- -- | Examples
-- setSyn :: String
-- setSyn = intercalate "\n" $
--   [ "signature Set() where"
--   , "  set X"
--   , "end"
--   ]

-- set :: SigDef
-- set = SigDef "Set" $ SigLam
--   { _sigLamArgs = []
--   , _sigBody =
--     [ SigDeclSet "X"
--     ]
--   }

-- setsSyn = ((setSyn ++ "\n\n") ++) $ intercalate "\n" $
--   [ "signature Sets() where"
--   , "  set X;"
--   , "  set Y;"
--   , "  set Z"
--   , "end"
--   ]

-- sets :: SigDef
-- sets = SigDef "Sets" $ SigLam
--   { _sigLamArgs = []
--   , _sigBody =
--     [ SigDeclSet "X"
--     , SigDeclSet "Y"
--     , SigDeclSet "Z"
--     ]
--   }

-- setsModuleSyn = intercalate "\n" $
--   [ "module FanOut(A : Set()) : Sets() where"
--   , "  set X = A.X;"
--   , "  set Y = A.X;"
--   , "  set Z = A.X"
--   , "end"
--   ]

-- badSetsSyn = ((setSyn ++ "\n\n") ++) $ intercalate "\n" $
--   [ "signature Sets() where"
--   , "  set X;"
--   , "  set Y;"
--   , "  set X"
--   , "end"
--   ]

-- badSets = SigDef "Sets" $ SigLam
--   { _sigLamArgs = []
--   , _sigBody =
--     [ SigDeclSet "X"
--     , SigDeclSet "Y"
--     , SigDeclSet "X"
--     ]
--   }




-- functionSyn = intercalate "\n" $
--   [ "signature Fun() where"
--   , "  set X;"
--   , "  set Y;"
--   , "  fun f : X -> Y"
--   , "end"
--   ]
-- function :: SigDef
-- function = SigDef "Fun" $ SigLam
--   { _sigLamArgs = []
--   , _sigBody =
--     [ SigDeclSet "X"
--     , SigDeclSet "Y"
--     , SigDeclFun "f" (FunType (SetExp (ModDeref Nothing "X")) (SetExp (ModDeref Nothing "Y")))
--     ]
--   }

-- fun2Syn = intercalate "\n" $
--   [ "signature Fun() where"
--   , "  set X;"
--   , "  fun f : X -> X;"
--   , "  set Y"
--   , "end"
--   ]

-- fun2 = SigDef "Fun" $ SigLam
--   { _sigLamArgs = []
--   , _sigBody =
--     [ SigDeclSet "X"
--     , SigDeclFun "f" (FunType (SetExp (ModDeref Nothing "X")) (SetExp (ModDeref Nothing "X")))
--     , SigDeclSet "Y"
--     ]
--   }

-- badfunSyn = intercalate "\n" $
--   [ "signature Fun() where"
--   , "  set X;"
--   , "  fun f : X -> Y"
--   , "end"
--   ]
-- badfun = SigDef "Fun" $ SigLam
--   { _sigLamArgs = []
--   , _sigBody =
--     [ SigDeclSet "X"
--     , SigDeclFun "f" (FunType (SetExp (ModDeref Nothing "X")) (SetExp (ModDeref Nothing "Y")))
--     ]
--   }

-- extfunSyn = intercalate "\n" $
--   [ "signature Endo(A: Set()) where"
--   , "  fun f : A.X -> A.X"
--   , "end"
--   ]
-- extfun = SigDef "Endo" $ SigLam
--   { _sigLamArgs = [ ("A", seapp (SEName "Set") [])]
--   , _sigBody =
--     [ SigDeclFun "f" (FunType (SetExp (ModDeref (Just (ModBase (Bound "A"))) "X")) (SetExp (ModDeref (Just (ModBase $ Bound "A")) "X")))
--     ]
--   }

-- badextfunSyn = intercalate "\n" $
--   [ "signature Endo(A: Set()) where"
--   , "  fun f : A.Y -> A.Y"
--   , "end"
--   ]
-- badextfun = SigDef "Endo" $ SigLam
--   { _sigLamArgs = [ ("A", seapp (SEName "Set") [])]
--   , _sigBody =
--     [ SigDeclFun "f" (FunType (SetExp (ModDeref (Just (ModBase $ Bound "A")) "Y")) (SetExp (ModDeref (Just (ModBase $ Bound "A")) "Y")))
--     ]
--   }

-- tricky_modSyn = intercalate "\n" $
--   [ setSyn
--   , "signature Weird-Endo(A : Set()) where"
--   , "  set X;"
--   , "  fun e : A.X -> A.X"
--   , "end"
--   , ""
--   , "module E1(A : Set()) : Weird-Endo(A) where"
--   , "  set X = A.X;"
--   , "  fun e(x) = x"
--   , "end"
--   , ""
--   -- , "module E2(A : Set, E : Weird-Endo(E1(A).X)) : Weird-Endo(A) where"
--   -- , "  set X = A.X;"
--   -- , "  fun e(x) = E1(A).e(x)"
--   -- , "end"
--   ]
-- tricky_mod =
--   [ TLSig $ set
--   , TLSig $ SigDef "Weird-Endo" $ SigLam
--     { _sigLamArgs = [("A", seapp (SEName "Set") [])]
--     , _sigBody =
--       [ SigDeclSet "X"
--       , SigDeclFun "e" (FunType (SetExp (ModDeref (Just $ ModBase $ Bound "A") "X"))
--                                 (SetExp (ModDeref (Just $ ModBase $ Bound "A") "X")))
--       ]
--     }
--   , TLMod $ ModDef "E1" $ ModLam
--     { _modLamParams = [("A", seapp (SEName "Set") [])]
--     , _modOSig  = seapp (SEName "Weird-Endo") [ ModBase $ Bound "A" ]
--     , _modBody =
--       [ ModDeclSet "X" (SetExp (ModDeref (Just $ ModBase $ Bound "A") "X"))
--       , ModDeclFun "e" "x" (EEVar "x")
--       ]
--     }
--   ]

-- fun_comp_ex = intercalate "\n" $
--   [ setSyn
--   , "signature Function(A : Set(), B : Set()) where"
--   , "  fun f : A.X -> B.X"
--   , "end"
--   , "module Id(A : Set()) : Function(A, A) where"
--   , "  fun f(x) = x"
--   , "end"
--   , "module Comp(A : Set(), B : Set(), C:Set(), F: Function(A,B), G :Function(B,C)) : Function(A,C) where"
--   , "  fun f(a) = G.f(F.f(a))"
--   , "end"
--   ]

-- fun_comp_tree =
--   [ TLSig $ set
--   , TLSig $ SigDef "Function" $ SigLam
--     { _sigLamArgs = [("A", seapp (SEName "Set") []), ("B", seapp (SEName "Set") [])]
--     , _sigBody =
--       [ SigDeclFun "f" (FunType (SetExp (ModDeref (Just $ ModBase $ Bound "A") "X"))
--                                 (SetExp (ModDeref (Just $ ModBase $ Bound "B") "X")))
--       ]
--     }
--   , TLMod $ ModDef "Id" $ ModLam
--     { _modLamParams = [("A", seapp (SEName "Set") [])]
--     , _modOSig  = seapp (SEName "Function") [ ModBase $ Bound "A" , ModBase $ Bound "A"]
--     , _modBody =
--       [ ModDeclFun "f" "x" (EEVar "x")
--       ]
--     }
--   , TLMod $ ModDef "Comp" $ ModLam
--     { _modLamParams = [ ("A", seapp (SEName "Set") [])
--                     , ("B", seapp (SEName "Set") [])
--                     , ("C", seapp (SEName "Set") [])
--                     , ("F", seapp (SEName "Function") [ModBase . Bound $ "A", ModBase . Bound $ "B"])
--                     , ("G", seapp (SEName "Function") [ModBase . Bound $ "B", ModBase . Bound $ "C"])]
--     , _modOSig  = seapp (SEName "Function") [ ModBase . Bound $ "A" , ModBase . Bound $ "C"]
--     , _modBody =
--       [ ModDeclFun "f" "a" (EEApp (ModDeref (Just $ ModBase . Bound $ "G") "f") . EEApp (ModDeref (Just $ ModBase . Bound $ "F") "f") $ EEVar "a")
--       ]
--     }
--   ]

-- category :: SigDef
-- category =
--   SigDef "Category" $ SigLam
--   { _sigLamArgs = [ ]
--   , _sigBody =
--     [ SigDeclSet "Ob"
--     -- , SigDeclSpan "Arr" (SetExp (ModDeref (ModBase "Category") "Ob")) (SetExp (ModDeref (ModBase "Category") "Ob"))
--     -- , SigDeclTerm "id" (TermFunType "forall a. Arr(a,a)")
--     -- , SigDeclTerm "comp" (TermFunType "forall a,b,c. (Arr(a,b), Arr(b,c)) -> Arr(a,c)")
--     -- , SigDeclAx   "id-left" (TermFunType "forall a,b. (Arr(a,b)) -> Arr(a,b)") TermExp TermExp
--     -- | TODO: id-right, assoc
--     ]
--   }

-- fctor :: SigDef
-- fctor =
--   SigDef "Functor" $ SigLam
--   { _sigLamArgs = [ ("C", seapp (SEName "Category") [])
--                   , ("D", seapp (SEName "Category") [])
--                   ]
--   , _sigBody = []
--   }

-- -- | Error: C undefined
-- bad_trans :: SigDef
-- bad_trans =
--   SigDef "Bad Trans" $ SigLam
--   { _sigLamArgs = [ ("F", seapp (SEName "Functor") [ModBase . Bound $ "C", ModBase . Bound $ "D"])]
--   , _sigBody = []
--   }
-- badTrans2 :: SigDef
-- badTrans2 =
--   SigDef "Bad Trans" $ SigLam
--   { _sigLamArgs = [ ("F", seapp (SEName "Functor") [])]
--   , _sigBody = []
--   }
-- badTrans3 :: SigDef
-- badTrans3 =
--   SigDef "Bad Trans" $ SigLam
--   { _sigLamArgs = [ ("F", seapp (SEName "Functor") [ModBase . Bound $ "F", ModBase . Bound $ "F"])]
--   , _sigBody = []
--   }

-- badTrans4 :: SigDef
-- badTrans4 =
--   SigDef "Bad Trans" $ SigLam
--   { _sigLamArgs = [ ("A", seapp (SEName "Category") [])
--                   , ("B", seapp (SEName "Category") [])
--                   , ("F", seapp (SEName "Functor")  [ModBase . Bound $ "A", ModBase . Bound $ "B"])
--                   , ("G", seapp (SEName "Functor") [ModBase . Bound $ "F", ModBase . Bound $ "F"])
--                   ]
--   , _sigBody = []
--   }
  

-- trans :: SigDef
-- trans =
--   SigDef "Natural-Transformation" $ SigLam
--   { _sigLamArgs = [ ("A", seapp (SEName "Category") [])
--                   , ("B", seapp (SEName "Category") [])
--                   , ("F", seapp (SEName "Functor")  [ModBase . Bound $ "A", ModBase . Bound $ "B"])
--                   , ("G", seapp (SEName "Functor")  [ModBase . Bound $ "A", ModBase . Bound $ "B"])
--                   ]
--   , _sigBody = []
--   }

-- weird :: SigDef
-- weird =
--   SigDef "2-Cell" $ SigLam
--   { _sigLamArgs = [ ("A", seapp (SEName "Category") [])
--                   , ("B", seapp (SEName "Category") [])
--                   , ("C", seapp (SEName "Category") [])
--                   , ("F", seapp (SEName "Functor")  [ModBase . Bound $ "A", ModBase . Bound $ "B"])
--                   , ("G", seapp (SEName "Functor")  [ModBase . Bound $ "B", ModBase . Bound $ "C"])
--                   , ("alpha", seapp (SEName "Natural-Transformation") [ModBase . Bound $ "A", ModBase . Bound $ "B", ModBase . Bound $ "F", ModBase . Bound $ "G"])
--                   ]
--   , _sigBody = []
--   }


-- clofctor = subst (TLSig category) fctor
-- clobad = subst (TLSig clofctor) . subst (TLSig category) $ badTrans4

-- spanSyn = intercalate "\n" $
--   [ "signature Span(A : Set(), B : Set()) where"
--   , "  span M : A.X ~~ B.X"
--   , "end"
--   ]
-- restrictSyn = intercalate "\n" $
--   [ "module Restrict(A : Set(), A' : Set(), B : Set(), B' : Set(), F : Fun(A,A'), G : Fun(B,B'), R : Span(A',B')) : Span(A,B) where"
--   , "  span M(a,b) = R.M(F.f(a), G.f(b))"
--   , "end"
--   ]

-- -- | Module Tests
-- modTestSig = intercalate "\n"
--   [ "signature Preamble() where"
--   , "  set X;"
--   , "  set Y;"
--   , "  set Z;"
--   , "  fun f : X -> Y;"
--   , "  fun g : Y -> X;"
--   , "  fun h : Y -> Z"
--   , "end"
--   , "signature Main() where"
--   , "  set X"
--   , ";  set Z"
--   , ";  fun p : X -> Z"
--   , "end"
--   ]

-- modTest1 = tried
--   where Right tried = parse program "test" $ intercalate "\n"
--           [ modTestSig
--           , "module M(P : Preamble()) : Main() where"
--           , "  set X = P.X"
--           , ";  set Z = P.X"
--           , ";  fun p(x) = x"
--           , "end"
--           ]
-- modTest2Syn =           intercalate "\n"
--           [ modTestSig
--           , "module M(P : Preamble()) : Main() where"
--           , "  set X = P.X"
--           , ";  set Z = P.Y"
--           , ";  fun p(x) = P.f(x)"
--           , "end"
--           ]
-- modTest2 = tried
--   where Right tried = parse program "test" $ modTest2Syn
-- modTest3 = tried
--   where Right tried = parse program "test" $ intercalate "\n"
--           [ modTestSig
--           , "module M(P : Preamble()) : Main() where"
--           , "  set X = P.X"
--           , ";  set Z = P.Z"
--           , ";  fun p(x) = P.h(P.f(x))"
--           , "end"
--           ]
-- modTest4 = tried
--   where Right tried = parse program "test" $ intercalate "\n"
--           [ modTestSig
--           , "module M(P : Preamble()) : Main() where"
--           , "  set X = P.X"
--           , ";  set Z = P.Z"
--           , ";  fun p(x) = P.h(P.f(P.g(P.f(x))))"
--           , "end"
--           ]
-- -- | Failing Modules
-- mainSyn p = intercalate "\n"
--   [ modTestSig
--   , "module M(P: Preamble()) : Main() where"
--   , p
--   , "end"
--   ]
-- fromRight (Right x) = x
-- wrongOrder = fromRight $ parse program "test" wrongOrderModSyn
-- wrongOrderModSyn = mainSyn . intercalate "\n" $
--   [ "  set Z = P.Y"
--   , "; set X = P.Y"
--   , "; fun p(x) = x"
--   ]
-- wrongVar = fromRight $ parse program "test" wrongVarModSyn
-- wrongVarModSyn = mainSyn . intercalate "\n" $
--   [ "  set X = P.X"
--   , ";  set Z = P.Y"
--   , ";  fun p(x) = P.f(y)"
--   ]
-- badField = fromRight $ parse program "test" badFieldModSyn
-- badFieldModSyn = mainSyn . intercalate "\n" $
--   [ "  set X = P.X"
--   , ";  set Z = P.Y"
--   , ";  fun p(x) = P.l(y)"
--   ]
-- badTypeFun = fromRight $ parse program "test" badTypeFunModSyn
-- badTypeFunModSyn = mainSyn . intercalate "\n" $
--   [ "  set X = P.X"
--   , ";  set Z = P.X"
--   , ";  fun p(x) = P.f(x)"
--   ]

-- -- | Simple Span Tests
-- spanmod0 = itParses spanPreamble
-- spanPreamble = intercalate "\n" $
--   [ "signature Preamble() where"
--   , "   set A"
--   , ";  set A'"
--   , ";  set B"
--   , ";  set B'"
--   , ";  fun f : A -> A'"
--   , ";  fun g : B -> B'"
--   , ";  fun ae : A -> A"
--   , ";  fun be : B -> B"
--   , ";  span R : A' ~~ B'"
--   , "end"
--   , "signature Main() where"
--   , "   set X"
--   , ";  set Y"
--   , ";  span Q : X ~~ Y"
--   , "end"
--   ]

-- spanMainSyn p = intercalate "\n" $
--   [ spanPreamble
--   , "module M(P : Preamble()) : Main() where"
--   , p
--   , "end"
--   ]

-- itParses = fromRight . parse program "test"
-- spanmod1 = itParses simpSpan
-- simpSpan = spanMainSyn . intercalate "\n" $
--   [ "   set X = P.A'"
--   , ";  set Y = P.B'"
--   , ";  span Q(a', b') = P.R(a', b')"
--   ]
-- spanmod2 = itParses restrictSpan
-- restrictSpan = spanMainSyn . intercalate "\n" $
--   [ "   set X = P.A"
--   , ";  set Y = P.B"
--   , ";  span Q(a, b) = P.R(P.f(a), P.g(b))"
--   ]
-- spanmod3 = itParses restrictSpan2
-- restrictSpan2 = spanMainSyn . intercalate "\n" $
--   [ "   set X = P.A"
--   , ";  set Y = P.B"
--   , ";  span Q(a, b) = P.R(P.f(P.ae(a)), P.g(P.be(b)))"
--   ]
