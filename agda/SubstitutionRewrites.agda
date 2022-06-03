{-# OPTIONS --rewriting #-}

open import Lib

open import STC 

module SubstitutionRewrites where



  -- ----------------------------------------------------------------------
  -- ▹

  -- STRUCTURAL

  app▹subst-unit-both : {ℂ 𝔼 𝔻'' : Cat} {P : Rel ℂ 𝔼} {R : Rel ℂ 𝔼} 
                (s : vc ℂ ⊢ (P ▹ R))
                (a : Fun ℂ 𝔼)
                (t : vc ℂ ⊢ (P [ v ∣ a ]))
              → ∀ {h1 : Fun 𝔻'' ℂ}
              → _==_ 
                     (subst-tr (app▹ s a t) (vs h1))
                     ( (app▹ (s [ vs h1 ]tr) (a · h1) (t [ vs h1 ]tr)) )
  app▹subst-unit-both s a t {h1} = app▹subst s a t (vs h1) (vs h1) 

  app▹subst-unit-both-v : {ℂ 𝔻'' : Cat} {P : Rel ℂ ℂ} {R : Rel ℂ ℂ} 
                (s : vc ℂ ⊢ (P ▹ R))
                (t : vc ℂ ⊢ (P [ v ∣ v ]))
              → ∀ {h1 : Fun 𝔻'' ℂ}
              → _==_ 
                      (subst-tr (app▹ s v t) (vs h1))
                     ( (app▹ (s [ vs h1 ]tr) (h1) (t [ vs h1 ]tr)) )
  app▹subst-unit-both-v s t {h1} = app▹subst-unit-both s v t {h1}

  {-# REWRITE app▹subst-unit-both #-}
  {-# REWRITE app▹subst-unit-both-v #-}
  
  app▹subst-unitl-subst :
                {ℂ 𝔼 𝔼' 𝔻'' 𝔼'' : Cat} {P : Rel ℂ 𝔼} {R : Rel ℂ 𝔼} {ϕa : Ctx ℂ 𝔼'}
                (s : vc ℂ ⊢ (P ▹ R))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (P [ v ∣ a ]))
              → {ϕa' : Ctx 𝔻'' 𝔼''}
              → ∀ {h2 h4}
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ h4 ])
              → _==_ {_}{(ϕa') ⊢ (R [ h2 ∣ a · h4 ])}
                     (subst-tr (app▹ s a t) ϕ2)
                     ( (app▹ (s [ vs h2 ]tr) (a · h4) (t [ ϕ2 ]tr)) )
  app▹subst-unitl-subst s a t ϕ2 = app▹subst s a t (vs _) ϕ2

  app▹subst-unitl-subst-v :
                {ℂ 𝔼 𝔼' 𝔻'' 𝔼'' : Cat} {P : Rel ℂ 𝔼} {R : Rel ℂ 𝔼} {ϕa : Ctx ℂ 𝔼}
                (s : vc ℂ ⊢ (P ▹ R))
                (t : ϕa ⊢ P)
              → {ϕa' : Ctx 𝔻'' 𝔼''}
              → ∀ {h2 h4}
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ h4 ])
              → _==_ {_}{(ϕa') ⊢ (R [ h2 ∣ h4 ])}
                     (subst-tr (app▹ s v t) ϕ2)
                     ( (app▹ (s [ vs h2 ]tr) (h4) (t [ ϕ2 ]tr)) )
  app▹subst-unitl-subst-v s t ϕ2 = app▹subst s v t (vs _) ϕ2
{-
  app▹subst-unitl-subst-v4 :
                {ℂ 𝔼 𝔼' 𝔻'' : Cat} {P : Rel ℂ 𝔼} {R : Rel ℂ 𝔼} {ϕa : Ctx ℂ 𝔼'}
                (s : vc ℂ ⊢ (P ▹ R))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (P [ v ∣ a ]))
              → {ϕa' : Ctx 𝔻'' 𝔼'}
              → ∀ {h2}
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ v ])
              → _==_ {_}{(ϕa') ⊢ (R [ h2 ∣ a ])}
                     (subst-tr (app▹ s a t) ϕ2)
                     ( (app▹ (s [ vs h2 ]tr) (a) (t [ ϕ2 ]tr)) )
  app▹subst-unitl-subst-v4 s a t ϕ2 = app▹subst s a t (vs _) ϕ2

  app▹subst-unitl-subst-v4-v :
                {ℂ 𝔼 𝔻'' : Cat} {P : Rel ℂ 𝔼} {R : Rel ℂ 𝔼} {ϕa : Ctx ℂ 𝔼}
                (s : vc ℂ ⊢ (P ▹ R))
                (t : ϕa ⊢ P)
              → {ϕa' : Ctx 𝔻'' 𝔼}
              → ∀ {h2}
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ v ])
              → _==_ {_}{(ϕa') ⊢ (R [ h2 ∣ v ])}
                     (subst-tr (app▹ s v t) ϕ2)
                     ( (app▹ (s [ vs h2 ]tr) (v) (t [ ϕ2 ]tr)) )
  app▹subst-unitl-subst-v4-v s t ϕ2 = app▹subst s v t (vs _) ϕ2
-}
  app▹subst-unitr-subst : {ℂ 𝔻 𝔼 𝔻'' ℂ''  : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼} 
                (s : ϕf ⊢ (P ▹ R))
                (a : Fun 𝔻 𝔼)
                (t : vc 𝔻 ⊢ (P [ v ∣ a ]))
              → {ϕf' : Ctx ℂ'' 𝔻''} 
              → ∀ {h1 h2}
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → _==_ {_}{(ϕf') ⊢ (R [ h1 ∣ a · h2 ])}
                     (subst-tr (app▹ s a t) (ϕ1))
                     ( (app▹ (s [ ϕ1 ]tr) (a · h2) (t [ vs h2 ]tr)) )
  app▹subst-unitr-subst s a t ϕ1 = app▹subst s a t ϕ1 (vs _)

  app▹subst-unitr-subst-v : {ℂ 𝔻 𝔻'' ℂ''  : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔻 𝔻} {R : Rel ℂ 𝔻} 
                (s : ϕf ⊢ (P ▹ R))
                (t : vc 𝔻 ⊢ (P))
              → {ϕf' : Ctx ℂ'' 𝔻''} 
              → ∀ {h1 h2}
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → _==_ {_}{(ϕf') ⊢ (R [ h1 ∣ h2 ])}
                     (subst-tr (app▹ s v t) (ϕ1))
                     ( (app▹ (s [ ϕ1 ]tr) (h2) (t [ vs h2 ]tr)) )
  app▹subst-unitr-subst-v s t ϕ1 = app▹subst s v t ϕ1 (vs _)

  app▹subst-lassoc-subst : {ℂ 𝔻 𝔽 𝔽' 𝔼 𝔼' ℂ'' 𝔻'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔽} {ϕf2 : Ctx 𝔽 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
                (s : (ϕf ,, ϕf2) ⊢ (R ▹ P))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (R [ v ∣ a ]))
              → {ϕf' : Ctx ℂ'' 𝔽'} {ϕf'' : Ctx 𝔽' 𝔻''} {ϕa' : Ctx 𝔻'' 𝔼''}
              → ∀ {h1 h2 h3 h4}
              → (ϕ1 : (ϕf') ⊢s ϕf [ h1 ∣ h3 ])
              → (ϕ1' : (ϕf'') ⊢s ϕf2 [ h3 ∣ h2 ])
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ h4 ])
              → _==_ {_}{(ϕf' ,, (ϕf'' ,, ϕa')) ⊢ (P [ h1 ∣ a · h4 ])}
                     (subst-tr (app▹ s a t) (,,s _ ϕ1 (,,s _ ϕ1' ϕ2)))
                     ( (app▹ (s [ ,,s _ ϕ1 ϕ1' ]tr) (a · h4) (t [ ϕ2 ]tr)) )
  app▹subst-lassoc-subst s a t ϕ1 ϕ1' ϕ2 = app▹subst s a t (,,s _ ϕ1 ϕ1') ϕ2 

  {-# REWRITE app▹subst-lassoc-subst #-}
  {-# REWRITE app▹subst-unitl-subst-v #-}
  {-# REWRITE app▹subst-unitl-subst #-}
  {-# REWRITE app▹subst-unitr-subst #-}
  {-# REWRITE app▹subst-unitr-subst-v #-}

  -- SPECIAL CASES 

  -- not sure why adding these specifically as rewrites helps:
  -- they are just uses of app▹subst so *should* be implied by them?
  -- I think it's matching on the types


  app▹subst-v : {ℂ 𝔻 𝔼 ℂ'' 𝔻'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼}
                (s : ϕf ⊢ (P ▹ R))
                (t : ϕa ⊢ (P))
              → {ϕf' : Ctx ℂ'' 𝔻''} {ϕa' : Ctx 𝔻'' 𝔼''}
              → ∀ {h1 h2 h4}
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ h4 ])
              → _==_ {_}{(ϕf' ,, ϕa') ⊢ (R [ h1 ∣ h4 ])}
                     (subst-tr (app▹ s v t) (,,s _ ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (h4) (t [ ϕ2 ]tr)) )
  app▹subst-v s t ϕ1 ϕ2 = app▹subst s v t ϕ1 ϕ2 

  app▹subst-unitr : {ℂ 𝔻 𝔼 𝔼' ℂ'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
                (s : ϕf ⊢ (R ▹ P))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ R [ v ∣ a ])
              → {ϕf' : Ctx ℂ'' 𝔼''}
              → {fl : Fun ℂ'' ℂ} {fr : Fun 𝔼'' 𝔻} {ar : Fun 𝔼'' 𝔼'} 
              → (ϕ1 : ϕf' ⊢s ϕf [ fl ∣ fr ])
              → (ϕ2 : vc 𝔼'' ⊢s ϕa [ fr ∣ ar ])
              → _==_ {_}{(ϕf') ⊢ ((P [ v ∣ a ]) [ fl ∣ ar ])}
                     (subst-tr (app▹ s a t) (,,s fr ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (a · ar) (t [ ϕ2 ]tr)) )
  app▹subst-unitr s a t ϕ1 ϕ2  = app▹subst s a t ϕ1 ϕ2

  app▹subst-unitr-v : {ℂ 𝔻 𝔼 ℂ'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼}
                (s : ϕf ⊢ (R ▹ P))
                (t : ϕa ⊢ R)
              → {ϕf' : Ctx ℂ'' 𝔼''}
              → {fl : Fun ℂ'' ℂ} {fr : Fun 𝔼'' 𝔻} {ar : Fun 𝔼'' 𝔼} 
              → (ϕ1 : ϕf' ⊢s ϕf [ fl ∣ fr ])
              → (ϕ2 : vc 𝔼'' ⊢s ϕa [ fr ∣ ar ])
              → _==_ {_}{(ϕf') ⊢ ((P) [ fl ∣ ar ])}
                     (subst-tr (app▹ s v t) (,,s fr ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (ar) (t [ ϕ2 ]tr)) )
  app▹subst-unitr-v s t ϕ1 ϕ2  = app▹subst s v t ϕ1 ϕ2

  app▹subst-unitl : {ℂ 𝔻 𝔼 𝔼' ℂ''  𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
                (s : ϕf ⊢ (R ▹ P))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (R [ v ∣ a ]))
              → {ϕa' : Ctx ℂ'' 𝔼''}
              → ∀ {h1 h2 h4}
              → (ϕ1 : vc ℂ'' ⊢s ϕf [ h1 ∣ h2 ])
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ h4 ])
              → _==_ {_}{(ϕa') ⊢ (P [ h1 ∣ a · h4 ])}
                     (subst-tr (app▹ s a t) (,,s _ ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (a · h4) (t [ ϕ2 ]tr)) )
  app▹subst-unitl s a t ϕ1 ϕ2 = app▹subst s a t ϕ1 ϕ2 

  app▹subst-unitl-v : {ℂ 𝔻 𝔼 ℂ''  𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼}
                (s : ϕf ⊢ (R ▹ P))
                (t : ϕa ⊢ (R))
              → {ϕa' : Ctx ℂ'' 𝔼''}
              → ∀ {h1 h2 h4}
              → (ϕ1 : vc ℂ'' ⊢s ϕf [ h1 ∣ h2 ])
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ h4 ])
              → _==_ {_}{(ϕa') ⊢ (P [ h1 ∣ h4 ])}
                     (subst-tr (app▹ s v t) (,,s _ ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (h4) (t [ ϕ2 ]tr)) )
  app▹subst-unitl-v s t ϕ1 ϕ2 = app▹subst s v t ϕ1 ϕ2 

  app▹subst-lassoc-ctx : {ℂ 𝔻 𝔽 𝔼 𝔼' ℂ'' 𝔻'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
                (s : ϕf ⊢ (R ▹ P))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (R [ v ∣ a ]))
              → {ϕf' : Ctx ℂ'' 𝔽} {ϕf'' : Ctx 𝔽 𝔻''} {ϕa' : Ctx 𝔻'' 𝔼''}
              → ∀ {h1 h2 h4}
              → (ϕ1 : (ϕf' ,, ϕf'') ⊢s ϕf [ h1 ∣ h2 ])
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ h4 ])
              → _==_ {_}{(ϕf' ,, (ϕf'' ,, ϕa')) ⊢ (P [ h1 ∣ a · h4 ])}
                     (subst-tr (app▹ s a t) (,,s _ ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (a · h4) (t [ ϕ2 ]tr)) )
  app▹subst-lassoc-ctx s a t ϕ1 ϕ2 = app▹subst s a t ϕ1 ϕ2 

  app▹subst-unitr-ids : {ℂ 𝔻 𝔼 ℂ'' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} 
                (s : ϕf ⊢ (R ▹ P))
                (a : Fun 𝔻 𝔼)
                (t : vc 𝔻 ⊢ R [ v ∣ a ])
              → {ϕf' : Ctx ℂ'' 𝔻}
              → {fl : Fun ℂ'' ℂ} {fr : Fun 𝔻 𝔻} 
              → (ϕ1 : ϕf' ⊢s ϕf [ fl ∣ v ])
              → _==_ {_}{(ϕf') ⊢ ((P [ v ∣ a ]) [ fl ∣ v ])}
                     (subst-tr (app▹ s a t) (,,s {ϕ2 = vc 𝔻} v ϕ1 (ids)))
                     ( (app▹ (s [ ϕ1 ]tr) (a) (t [ ids ]tr)))
  app▹subst-unitr-ids s a t ϕ1 = app▹subst s a t ϕ1 ids

  app▹subst-unitl-ids : {ℂ 𝔼 𝔼'  𝔼'' : Cat} {R : Rel ℂ 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx ℂ 𝔼'}
                (s : vc ℂ ⊢ (R ▹ P))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (R [ v ∣ a ]))
              → {ϕa' : Ctx ℂ 𝔼''}
              → ∀ {h4}
              → (ϕ2 : ϕa' ⊢s ϕa [ v ∣ h4 ])
              → _==_ {_}{(ϕa') ⊢ (P [ v  ∣ a · h4 ])}
                     (subst-tr (app▹ s a t) (,,s {ϕ1 = vc ℂ} _ ids ϕ2))
                     ( (app▹ (s [ ids ]tr) (a · h4) (t [ ϕ2 ]tr)) )
  app▹subst-unitl-ids s a t ϕ1 = app▹subst s a t ids ϕ1 

  {-
  app▹subst-v-middle-right : {ℂ 𝔻 𝔼 𝔼' ℂ'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
                (s : ϕf ⊢ (P ▹ R))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (P [ v ∣ a ]))
              → {ϕf' : Ctx ℂ'' 𝔻} {ϕa' : Ctx 𝔻 𝔼'}
              → ∀ {h1}
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ v ])
              → (ϕ2 : ϕa' ⊢s ϕa [ v ∣ v ])
              → _==_ {_}{(ϕf' ,, ϕa') ⊢ (R [ h1 ∣ a ])}
                     (subst-tr (app▹ s a t) (,,s _ ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (a) (t [ ϕ2 ]tr)) )
  app▹subst-v-middle-right s a t ϕ1 ϕ2 = app▹subst s a t ϕ1 ϕ2
  -}
  {-# REWRITE app▹subst-v #-}
  {-# REWRITE app▹subst-unitl #-}
  {-# REWRITE app▹subst-unitr #-}
  {-# REWRITE app▹subst-unitr-v #-}
  {-# REWRITE app▹subst-unitl-v #-}
  {-# REWRITE app▹subst-lassoc-ctx #-}

  -- ----------------------------------------------------------------------
  -- ◃

  -- STRUCTURAL

  app◃subst-unitl-subst : {ℂ 𝔻 𝔼 ℂ'' 𝔻'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔼 ℂ} {R : Rel 𝔼 𝔻} 
                (s : ϕf ⊢ (R ◃ P))
                (a : Fun ℂ 𝔼)
                (t : vc ℂ ⊢ (P [ a ∣ v ]))
              → {ϕf' : Ctx ℂ'' 𝔻''} 
              → ∀ {h1 h2 }
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → _==_ {_}{(ϕf') ⊢ (R [ a · h1 ∣ h2 ])}
                     (subst-tr (app◃ a t s) (ϕ1))
                     ( (app◃ (a · h1) (t [ vs h1 ]tr) (s [ ϕ1 ]tr)) )
  app◃subst-unitl-subst s a t ϕ1 = app◃subst s a t ϕ1 (vs _)

  app◃subst-unitl-subst-v : {ℂ 𝔻 ℂ'' 𝔻'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel ℂ ℂ} {R : Rel ℂ 𝔻} 
                (s : ϕf ⊢ (R ◃ P))
                (t : vc ℂ ⊢ (P))
              → {ϕf' : Ctx ℂ'' 𝔻''} 
              → ∀ {h1 h2 }
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → _==_ {_}{(ϕf') ⊢ (R [ h1 ∣ h2 ])}
                     (subst-tr (app◃ v t s) (ϕ1))
                     ( (app◃ (h1) (t [ vs h1 ]tr) (s [ ϕ1 ]tr)) )
  app◃subst-unitl-subst-v s t ϕ1 = app◃subst-unitl-subst s v t ϕ1 

  {-# REWRITE app◃subst-unitl-subst #-}
  {-# REWRITE app◃subst-unitl-subst-v #-}

  -- SPECIAL CASES


  app◃subst-v : {ℂ 𝔻 𝔼 ℂ'' 𝔻'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔼 ℂ} {R : Rel 𝔼 𝔻} {ϕa : Ctx 𝔼 ℂ}
                (s : ϕf ⊢ (R ◃ P))
                (t : ϕa ⊢ (P))
              → {ϕf' : Ctx ℂ'' 𝔻''} {ϕa' : Ctx 𝔼'' ℂ''}
              → ∀ {h1 h2 h4}
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → (ϕ2 : ϕa' ⊢s ϕa [ h4 ∣ h1 ])
              → _==_ {_}{(ϕa' ,, ϕf') ⊢ (R [ h4 ∣ h2 ])}
                     (subst-tr (app◃ v t s) (,,s _ ϕ2 ϕ1))
                     ( (app◃ (h4) (t [ ϕ2 ]tr) (s [ ϕ1 ]tr)) )
  app◃subst-v s t ϕ1 ϕ2 = app◃subst s v t ϕ1 ϕ2

  {-# REWRITE app◃subst-v #-}

  app◃subst-unitr : {ℂ 𝔻 𝔼 𝔼' ℂ'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔼 ℂ} {R : Rel 𝔼 𝔻} {ϕa : Ctx 𝔼' ℂ}
                    (s : ϕf ⊢ (R ◃ P))
                    (a : Fun 𝔼' 𝔼)
                    (t : ϕa ⊢ (P [ a ∣ v ]))
                  → {ϕa' : Ctx 𝔼'' ℂ''}
                  → ∀ {h1 h2 h4}
                  → (ϕ1 : vc ℂ'' ⊢s ϕf [ h1 ∣ h2 ])
                  → (ϕ2 : ϕa' ⊢s ϕa [ h4 ∣ h1 ])
                  → _==_ {_}{(ϕa') ⊢ (R [ a · h4 ∣ v · h2 ])}
                         (subst-tr (app◃ a t s) (,,s _ ϕ2 ϕ1))
                         ( (app◃ (a · h4) (t [ ϕ2 ]tr) (s [ ϕ1 ]tr)) )
  app◃subst-unitr s v t ϕ1 ϕ2 = app◃subst s v t ϕ1 ϕ2

  app◃subst-unitr-v : {ℂ 𝔻 𝔼 ℂ'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔼 ℂ} {R : Rel 𝔼 𝔻} {ϕa : Ctx 𝔼 ℂ}
                    (s : ϕf ⊢ (R ◃ P))
                    (t : ϕa ⊢ (P))
                  → {ϕa' : Ctx 𝔼'' ℂ''}
                  → ∀ {h1 h2 h4}
                  → (ϕ1 : vc ℂ'' ⊢s ϕf [ h1 ∣ h2 ])
                  → (ϕ2 : ϕa' ⊢s ϕa [ h4 ∣ h1 ])
                  → _==_ {_}{(ϕa') ⊢ (R [  h4 ∣ v · h2 ])}
                         (subst-tr (app◃ v t s) (,,s _ ϕ2 ϕ1))
                         ( (app◃ (h4) (t [ ϕ2 ]tr) (s [ ϕ1 ]tr)) )
  app◃subst-unitr-v s t ϕ1 ϕ2 = app◃subst s v t ϕ1 ϕ2

  {-# REWRITE app◃subst-unitr #-}
  {-# REWRITE app◃subst-unitr-v #-}

  app◃subst-unitl : {ℂ 𝔻 𝔼 𝔼' ℂ'' 𝔻'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔼 ℂ} {R : Rel 𝔼 𝔻} {ϕa : Ctx 𝔼' ℂ}
                (s : ϕf ⊢ (R ◃ P))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (P [ a ∣ v ]))
              → {ϕf' : Ctx ℂ'' 𝔻''} 
              → ∀ {h1 h2 h4}
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → (ϕ2 : vc ℂ'' ⊢s ϕa [ h4 ∣ h1 ])
              → _==_ {_}{(ϕf') ⊢ (R [ a · h4 ∣ v · h2 ])}
                     (subst-tr (app◃ a t s) (,,s _ ϕ2 ϕ1))
                     ( (app◃ (a · h4) (t [ ϕ2 ]tr) (s [ ϕ1 ]tr)) )
  app◃subst-unitl s a t ϕ1 ϕ2 = app◃subst s a t ϕ1 ϕ2

  app◃subst-unitl-v : {ℂ 𝔻 𝔼 ℂ'' 𝔻'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔼 ℂ} {R : Rel 𝔼 𝔻} {ϕa : Ctx 𝔼 ℂ}
                (s : ϕf ⊢ (R ◃ P))
                (t : ϕa ⊢ (P))
              → {ϕf' : Ctx ℂ'' 𝔻''} 
              → ∀ {h1 h2 h4}
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → (ϕ2 : vc ℂ'' ⊢s ϕa [ h4 ∣ h1 ])
              → _==_ {_}{(ϕf') ⊢ (R [ h4 ∣ h2 ])}
                     (subst-tr (app◃ v t s) (,,s _ ϕ2 ϕ1))
                     ( (app◃ (h4) (t [ ϕ2 ]tr) (s [ ϕ1 ]tr)) )
  app◃subst-unitl-v s t ϕ1 ϕ2 = app◃subst s v t ϕ1 ϕ2

  {-# REWRITE app◃subst-unitl #-}
  {-# REWRITE app◃subst-unitl-v #-}

  -- ----------------------------------------------------------------------
  -- morphism

  mor-recβ' : {ℂ 𝔻 : Cat} (Q : Rel ℂ ℂ)
             (t : ∀e Q)
             (c : Fun 𝔻 ℂ) 
           → _==_ {_} (app▹ (appe (mor-rec Q t) c ) c (ident c)) (appe t c)
  mor-recβ' {ℂ}{𝔻} Q t c =  ap (\ H → appe H c) (mor-recβ Q t) 

  mor-recβ'-v : {ℂ 𝔻 : Cat} (Q : Rel ℂ ℂ)
             (t : ∀e Q)
           → _==_ {_} (app▹ (appe (mor-rec Q t) v ) v (ident v)) (appe t v)
  mor-recβ'-v {ℂ}{𝔻} Q t =  mor-recβ' Q t v

  {-# REWRITE mor-recβ' #-}
  {-# REWRITE mor-recβ'-v #-}

  -- ----------------------------------------------------------------------
  -- ⊙

  ⊙-recβ' : ∀ {ℂ 𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
              (s : (P ⊸ (Q ▹ R)))
           → ∀ {ℂ' 𝔻' 𝔼' f1 f2 f3}
               {ϕ1 : Ctx ℂ' 𝔻'}  {ϕ2 : Ctx 𝔻' 𝔼'}  
               (x : ϕ1 ⊢ P [ f1 ∣ f2 ])
               (y : ϕ2 ⊢ Q [ f2 ∣ f3 ])
          → _==_{_}{ (ϕ1 ,, ϕ2) ⊢ R [ f1 ∣ f3 ]}
                ((app▹ (appe (⊙-rec s) f1) f3 (pair⊙ f2 x y)))
                ((app▹ (app▹ (appe s f1) f2 x) f3 y ))
  ⊙-recβ' {ℂ} {𝔻} {𝔼} {P} {Q } {R} s {ℂ'} {𝔻'} {𝔼'} {f1} {f2} {f3} {ϕ1} {ϕ2} x y =
           ap (\ s → (app▹ (app▹ (appe s f1) f2 x) f3 y )) (⊙-recβ s) ∘
            ap (app▹ (appe (isIso.g ⊙-rec-iso s) f1) f3) ( naturality? x y ) 

  -- SPECIAL CASES 

  ⊙-recβ'-allv : ∀ {ℂ 𝔻 𝔼 : Cat} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
              (s : (P ⊸ (Q ▹ R)))
           → ∀ 
               {ϕ1 : Ctx ℂ 𝔻}  {ϕ2 : Ctx 𝔻 𝔼}  
               (x : ϕ1 ⊢ P )
               (y : ϕ2 ⊢ Q )
          → _==_{_}{ (ϕ1 ,, ϕ2) ⊢ R }
                ((app▹ (appe (⊙-rec s) v) v (app▹ (app▹ (appe ⊙i* v) v x) v y)))
                ((app▹ (app▹ (appe s v) v x) v y ))
  ⊙-recβ'-allv s x y = ⊙-recβ' s x y

  ⊙-recβ'-unitl : ∀ {ℂ 𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
              (s : (P ⊸ (Q ▹ R)))
           → ∀ {ℂ' 𝔼' f1 f2 f3}
               {ϕ2 : Ctx ℂ' 𝔼'}  
               (x : vc ℂ' ⊢ P [ f1 ∣ f2 ])
               (y : ϕ2 ⊢ Q [ f2 ∣ f3 ])
          → _==_{_}{ (ϕ2) ⊢ R [ f1 ∣ f3 ]}
                ((app▹ (appe (⊙-rec s) f1) f3 (pair⊙ f2 x y)))
                ((app▹ (app▹ (appe s f1) f2 x) f3 y ))
  ⊙-recβ'-unitl s x y = ⊙-recβ' s x y

  ⊙-recβ'-unitl-allv : ∀ {ℂ 𝔻 : Cat} {P : Rel ℂ ℂ} {Q : Rel ℂ 𝔻} {R : Rel ℂ 𝔻}
              (s : (P ⊸ (Q ▹ R)))
           → ∀ {ϕ2 : Ctx ℂ 𝔻}  
               (x : vc ℂ ⊢ P )
               (y : ϕ2 ⊢ Q )
          → _==_{_}{ (ϕ2) ⊢ R }
                ((app▹ (appe (⊙-rec s) v) v (pair⊙ v x y)))
                ((app▹ (app▹ (appe s v) v x) v y ))
  ⊙-recβ'-unitl-allv s x y = ⊙-recβ' s x y

  ⊙-recβ'-unitr : ∀ {ℂ 𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
              (s : (P ⊸ (Q ▹ R)))
           → ∀ {ℂ' 𝔻' f1 f2 f3}
               {ϕ1 : Ctx ℂ' 𝔻'}  
               (x : ϕ1 ⊢ P [ f1 ∣ f2 ])
               (y : vc 𝔻' ⊢ Q [ f2 ∣ f3 ])
          → _==_{_}{ (ϕ1) ⊢ R [ f1 ∣ f3 ]}
                ((app▹ (appe (⊙-rec s) f1) f3 (pair⊙ f2 x y)))
                ((app▹ (app▹ (appe s f1) f2 x) f3 y ))
  ⊙-recβ'-unitr s x y = ⊙-recβ' s x y

  ⊙-recβ'-unitr-allv : ∀ {ℂ 𝔻 : Cat} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔻} {R : Rel ℂ 𝔻}
              (s : (P ⊸ (Q ▹ R)))
           → ∀ 
               {ϕ1 : Ctx ℂ 𝔻}  
               (x : ϕ1 ⊢ P )
               (y : vc 𝔻 ⊢ Q)
          → _==_{_}{ (ϕ1) ⊢ R}
                ((app▹ (appe (⊙-rec s) v) v (pair⊙ v x y)))
                ((app▹ (app▹ (appe s v) v x) v y ))
  ⊙-recβ'-unitr-allv s x y = ⊙-recβ' s x y

  {-# REWRITE ⊙-recβ' #-}
  {-# REWRITE ⊙-recβ'-unitl #-}
  {-# REWRITE ⊙-recβ'-unitl-allv #-}
  {-# REWRITE ⊙-recβ'-unitr #-}
  {-# REWRITE ⊙-recβ'-unitr-allv #-}
  {-# REWRITE ⊙-recβ'-allv #-}


