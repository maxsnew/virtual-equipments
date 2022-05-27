{-# OPTIONS --rewriting #-}

open import Lib

module Ordered where

  postulate 
    Rel : Set

  -- --------------------------------------------------------------------
  -- "relation contexts" as joinlists

  postulate
    Ctx : Set
    [_]    :  Rel → Ctx
    _,,_   :  Ctx → Ctx → Ctx
    vc     :  Ctx
    cunitr : (ϕ : Ctx) → (ϕ ,, vc) == ϕ
    cunitl : (ϕ : Ctx) → (vc ,, ϕ) == ϕ
    cassoc : (ϕ1 : Ctx) (ϕ2 : Ctx) (ϕ3 : Ctx)
           → ((ϕ1 ,, ϕ2) ,, ϕ3) == (ϕ1 ,, (ϕ2 ,, ϕ3))

  {-# REWRITE cunitl #-}
  {-# REWRITE cunitr #-}
  {-# REWRITE cassoc #-}

  -- --------------------------------------------------------------------
  -- transformation terms

  postulate 
    _⊢_ : Ctx → Rel → Set
    vt : {R : Rel} → [ R ] ⊢ R

  -- --------------------------------------------------------------------
  -- transformation substitutions (squares)

  postulate
    _⊢s_ : Ctx → Ctx → Set
    [_]s   : {ϕ : Ctx} {R : Rel}
           → ϕ ⊢ R
           → ϕ ⊢s ([ R ])
    vs     : vc ⊢s vc
    ,,s  : ∀ {ϕ1 : Ctx} {ϕ2 : Ctx}
             {Ψ1 : Ctx} {Ψ2 : Ctx}
           → ϕ1 ⊢s Ψ1 
           → ϕ2 ⊢s Ψ2 
           → (ϕ1 ,, ϕ2) ⊢s (Ψ1 ,, Ψ2) 
    ids   :  {ϕ : Ctx} → ϕ ⊢s ϕ 
    comps : {ϕ1 : Ctx} {ϕ2 : Ctx}  {ϕ3 : Ctx}
          → ϕ1 ⊢s ϕ2 
          → ϕ2 ⊢s ϕ3 
          → ϕ1 ⊢s ϕ3 
    -- TODO associativity, unit, interchange, def id and comp
{-
    ,,s-assoc  : ∀ {ℂ 𝔻 𝔼 ℂ' 𝔻' 𝔼' 𝔽 𝔽'}
                 {ϕ1 : Ctx ℂ 𝔻} {ϕ2 : Ctx 𝔻 𝔼} {ϕ3 : Ctx 𝔼 𝔽}
                 {Ψ1 : Ctx ℂ' 𝔻'} {Ψ2 : Ctx 𝔻' 𝔼'} {Ψ3 : Ctx 𝔼' 𝔽'}
                 {c : Fun ℂ ℂ'} (d : Fun 𝔻 𝔻') {e : Fun 𝔼 𝔼'} {f : Fun 𝔽 𝔽'}
                 → (f1 : ϕ1 ⊢s Ψ1 [ c ∣ d ])
                 → (f2 : ϕ2 ⊢s Ψ2 [ d ∣ e ])
                 → (f3 : ϕ3 ⊢s Ψ3 [ e ∣ f ])
                 → (,,s _ (,,s _ f1 f2) f3) == (,,s _ f1 (,,s _ f2 f3))
-}
    ,,s-unitr  : 
             {ϕ1 : Ctx} 
             {Ψ1 : Ctx}
           → (f : ϕ1 ⊢s Ψ1)
           → (,,s f (vs)) == f
    ,,s-unitl  : ∀
             {ϕ1 : Ctx} 
             {Ψ1 : Ctx}
           → (f : ϕ1 ⊢s Ψ1)
           → (,,s (vs) f) == f
    ids-vc : ids {vc} == vs

    comps-unit-r : {ϕ1 : Ctx} {ϕ2 : Ctx}  
          → (s : ϕ1 ⊢s ϕ2)
          → comps s ids == s

    comps-unit-l : {ϕ1 : Ctx} {ϕ2 : Ctx}  
          → (s : ϕ1 ⊢s ϕ2)
          → comps ids s == s

    comps-vs : {ϕ1 : Ctx}
             → (s : ϕ1 ⊢s vc)
             → comps s vs == s
           
  -- --------------------------------------------------------------------
  -- substitution into a term

  postulate
    subst-tr : 
              {ϕ : Ctx}
              {Ψ : Ctx}
              {R : Rel}
           →  Ψ ⊢ R
           →  ϕ ⊢s Ψ 
           →  ϕ ⊢ R 

  _[_]tr :  {ϕ : Ctx}
              {Ψ : Ctx}
              {R : Rel}
           →  Ψ ⊢ R
           →  ϕ ⊢s Ψ 
           →  ϕ ⊢ R 
  _[_]tr = subst-tr

  postulate
      fuse :{ϕ1 : Ctx} {ϕ2 : Ctx}  {ϕ3 : Ctx}
          → (s1 : ϕ1 ⊢s ϕ2 )
          → (s2 : ϕ2 ⊢s ϕ3 )
          → {R : Rel }
          → (t : ϕ3 ⊢ R)
          → (subst-tr (subst-tr t s2) s1) == (t [ comps s1 s2 ]tr)

      subst-ident : {ϕ1 : Ctx} {R : Rel} 
                  → (s : ϕ1 ⊢ R )
                  → subst-tr s ids == s

      subst-vt : {ϕ1 : Ctx} {R : Rel} 
               → (s : ϕ1 ⊢ R )
               → subst-tr vt [ s ]s == s

      subst-ident-vs : {R : Rel} 
                     → (s : vc ⊢ R )
                     → subst-tr s vs == s

  -- --------------------------------------------------------------------
  -- hom types 

  postulate
    _▹_  : (R : Rel) (P : Rel) → Rel
    λ▹ :{ϕ : Ctx} {R : Rel} {P : Rel}
       → (ϕ ,, [ R ]) ⊢ P
       → ϕ ⊢ (R ▹ P)
    app▹ : {ϕf : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
           (s : ϕf ⊢ (R ▹ P))
           (t : ϕa ⊢ (R))
           → (ϕf ,, ϕa) ⊢ (P )
    β▹ : {ϕf : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
           (s : (ϕf ,, [ R ]) ⊢ P)
           (t : ϕa ⊢ (R ))
       → app▹ {ϕf = ϕf} {ϕa = ϕa} (λ▹ s) t == ( s [ ,,s {ϕ1 = ϕf} {ϕ2 = ϕa} ids ([ t ]s) ]tr)
    η▹ : {ϕ : Ctx } {R : Rel} {P : Rel}
       → (f : ϕ ⊢ (R ▹ P))
       → f == λ▹ (app▹ {ϕf = ϕ} {ϕa = [ R ]} f vt )
  postulate
    λ▹subst : {ϕ : Ctx} {R : Rel} {P : Rel}
       → (s : (ϕ ,, [ R ]) ⊢ P)
       → (ϕ' : Ctx )
       → (ϕ0 : ϕ' ⊢s ϕ )
       → (subst-tr (λ▹ s) ϕ0) == λ▹ (s [ ,,s ϕ0 [ vt ]s ]tr) 
       
    app▹subst : {ϕf : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
                (s : ϕf ⊢ (R ▹ P))
                (t : ϕa ⊢ (R))
              → {ϕf' : Ctx } {ϕa' : Ctx }
              → (ϕ1 : ϕf' ⊢s ϕf )
              → (ϕ2 : ϕa' ⊢s ϕa )
              → _==_ {_}{(ϕf' ,, ϕa') ⊢ (P)}
                     (subst-tr (app▹ s t) (,,s ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (t [ ϕ2 ]tr)) )

    app▹subst-unitl : {ϕf : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
                (s : ϕf ⊢ (R ▹ P))
                (t : ϕa ⊢ (R))
              → {ϕf' : Ctx } 
              → (ϕ1 : ϕf' ⊢s ϕf )
              → (ϕ2 : vc ⊢s ϕa )
              → _==_ {_}{(ϕf') ⊢ (P)}
                     (subst-tr (app▹ s t) (,,s ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (t [ ϕ2 ]tr)) )

    app▹subst-unitr : {ϕf : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx} 
                (s : ϕf ⊢ (R ▹ P))
                (t : ϕa ⊢ (R))
              → {ϕa' : Ctx } 
              → (ϕ1 : vc ⊢s ϕf )
              → (ϕ2 : ϕa' ⊢s ϕa )
              → _==_ {_}{(ϕa') ⊢ (P)}
                     (subst-tr (app▹ s t) (,,s ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (t [ ϕ2 ]tr)) )

  app▹subst-arg : {R : Rel} {P : Rel} {ϕa : Ctx}
                (s : vc ⊢ (R ▹ P))
                (t : ϕa ⊢ (R))
              → {ϕa' : Ctx }
              → (ϕ2 : ϕa' ⊢s ϕa )
              → _==_ {_}{(ϕa') ⊢ (P)}
                     (subst-tr {ϕa'} {ϕa} {P} (app▹ s t) (,,s {ϕ1 = vc} ids ϕ2))
                     ( (app▹ (s [ ids ]tr) (t [ ϕ2 ]tr)) )
  app▹subst-arg s t ϕ2 = app▹subst-unitr s t ids ϕ2

  app▹subst-fun : {R : Rel} {P : Rel} {ϕf : Ctx}
                (s : ϕf ⊢ (R ▹ P))
                (t : vc ⊢ (R))
              → {ϕf' : Ctx }
              → (ϕ1 : ϕf' ⊢s ϕf )
              → _==_ {_}{(ϕf') ⊢ (P)}
                     (subst-tr {ϕf'} {ϕf} {P} (app▹ s t) (,,s {ϕ1 = ϕf'} {ϕ2 = vc} ϕ1 ids))
                     ( (app▹ (s [ ϕ1 ]tr) (t [ ids ]tr)) )
  app▹subst-fun s t ϕ1 = app▹subst-unitl s t ϕ1 ids
{-
  -- app▹subst1 : {ℂ 𝔼 𝔼'' : Cat} {R : Rel ℂ 𝔼} {P : Rel ℂ 𝔼} 
  --               (s : (vc ℂ) ⊢ (R ▹ P))
  --               (a : Fun ℂ 𝔼 )
  --               (t : (vc ℂ) ⊢ (R [ v ∣ a ]))
  --             → ∀ {h4 : Fun 𝔼'' ℂ}
  --             → _==_ {_}
  --                    (subst-tr (app▹ s a t) (vs h4))
  --                    ( (app▹ (s [ vs h4 ]tr) (a · h4) (t [ vs h4 ]tr)) )
  -- app▹subst1 s a t {h4} = app▹subst s a t (vs h4) (vs h4) ∘ {!!}
-}

  postulate
    _◃_  : (R : Rel) (P : Rel) → Rel
    λ◃ : {ϕ : Ctx} {R : Rel} {P : Rel}
       → ([ P ] ,, ϕ) ⊢ R
       → ϕ ⊢ (R ◃ P)
    app◃ : {ϕa : Ctx} {ϕf : Ctx} {R : Rel} {P : Rel} 
           (t : ϕa ⊢ (P))
           (s : ϕf ⊢ (R ◃ P))
           → (ϕa ,, ϕf) ⊢ (R)
    β◃ : {ϕf : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
         (t : ϕa ⊢ (P))
         (s : ([ P ] ,, ϕf) ⊢ R)
        → app◃ {ϕa} {ϕf}  t (λ◃ s)  == (s [ ,,s {ϕ1 = ϕa}{ϕ2 = ϕf} [ t ]s ids ]tr)

    η◃ : {ϕ : Ctx } {R : Rel} {P : Rel}
       → (f : ϕ ⊢ (R ◃ P))
       → f == λ◃ (app◃  {ϕa = [ P ]} {ϕf = ϕ} vt f )

    λ◃subst : {ϕ : Ctx} {R : Rel} {P : Rel}
       → (s : ([ R ] ,, ϕ) ⊢ P)
       → (ϕ' : Ctx )
       → (ϕ0 : ϕ' ⊢s ϕ )
       → (subst-tr (λ◃ s) ϕ0) == λ◃ (s [ ,,s [ vt ]s ϕ0  ]tr) 

    app◃subst : {ϕf : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
                (s : ϕf ⊢ (P ◃ R))
                (t : ϕa ⊢ (R))
              → {ϕf' : Ctx } {ϕa' : Ctx }
              → (ϕ1 : ϕf' ⊢s ϕf )
              → (ϕ2 : ϕa' ⊢s ϕa )
              → _==_ {_}{(ϕa' ,, ϕf') ⊢ (P)}
                     (subst-tr (app◃ t s) (,,s ϕ2 ϕ1))
                     ( (app◃ (t [ ϕ2 ]tr) (s [ ϕ1 ]tr)) )

    app◃subst-arg : {R : Rel} {P : Rel} {ϕa : Ctx}
                (s : vc ⊢ (R ◃ P))
                (t : ϕa ⊢ (P))
              → {ϕa' : Ctx }
              → (ϕ2 : ϕa' ⊢s ϕa )
              → _==_ {_}{(ϕa') ⊢ (R)}
                     (subst-tr {ϕa'} {ϕa} (app◃ t s) (,,s {ϕ1 = ϕa'}{ϕ2 = vc} ϕ2 ids))
                     ( (app◃ (t [ ϕ2 ]tr) (s [ ids ]tr)) )

    app◃subst-fun : {R : Rel} {P : Rel} {ϕf : Ctx}
                (s : ϕf ⊢ (R ◃ P))
                (t : vc ⊢ (P))
              → {ϕf' : Ctx }
              → (ϕ1 : ϕf' ⊢s ϕf )
              → _==_ {_}{(ϕf') ⊢ (R)}
                     (subst-tr {ϕf'} {ϕf} (app◃ t s) (,,s {ϕ1 = vc} {ϕ2 = ϕf'} ids ϕ1))
                     ( (app◃ (t [ ids ]tr) (s [ ϕ1 ]tr)) )

    app◃subst-unitl : {ϕf : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
                (s : ϕf ⊢ (P ◃ R))
                (t : ϕa ⊢ (R))
              → {ϕf' : Ctx }
              → (ϕ1 : ϕf' ⊢s ϕf )
              → (ϕ2 : vc ⊢s ϕa )
              → _==_ {_}{(ϕf') ⊢ (P)}
                     (subst-tr (app◃ t s) (,,s ϕ2 ϕ1))
                     ( (app◃ (t [ ϕ2 ]tr) (s [ ϕ1 ]tr)) )

    app◃subst-unitr : {ϕf : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
                (s : ϕf ⊢ (P ◃ R))
                (t : ϕa ⊢ (R))
              → {ϕa' : Ctx } 
              → (ϕ1 : vc ⊢s ϕf )
              → (ϕ2 : ϕa' ⊢s ϕa )
              → _==_ {_}{(ϕa') ⊢ (P)}
                     (subst-tr (app◃ t s) (,,s ϕ2 ϕ1))
                     ( (app◃ (t [ ϕ2 ]tr) (s [ ϕ1 ]tr)) )

{-        
    -- FIXME: 
    -- η◃ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼}
    --    → (f : ϕ ⊢ (R ◃ P))
    --    → f == λ◃ (app◃ {ϕf = ϕ} {ϕa = [ R ]} f v vt )
    -- ◃subst : ∀ {ℂ' 𝔻' ℂ 𝔻 𝔼 : Cat} (R : Rel 𝔼 ℂ) (P : Rel 𝔼 𝔻)
    --            → (f : Fun ℂ' ℂ) (g : Fun 𝔻' 𝔻)
    --        → ( (R ◃ P) ) [ f ∣ g ] == ((R [ v ∣ f ]) ◃ (P [ v ∣ g ]))

  unλ◃ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx 𝔻 𝔼} {R : Rel ℂ 𝔼} {P : Rel ℂ 𝔻}
       → ϕ ⊢ (R ◃ P)
       → ([ P ] ,, ϕ) ⊢ R
  unλ◃ t =  app◃ v vt t 
-}

  -- ----------------------------------------------------------------------
  -- n.t. of profunctors
  
  _⊸_ : (P Q : Rel) → Set
  P ⊸ Q = (vc ⊢ (P ▹ Q))

  unλ⊸ : ∀ {P Q : Rel}
          → P ⊸ Q
          → [ P ] ⊢ Q
  unλ⊸ f = app▹ f vt

  _then⊸_ : ∀ {P Q R : Rel}
          → P ⊸ Q
          → Q ⊸ R
          → P ⊸ R
  f then⊸ g = (λ▹ (app▹ g (app▹ f vt) ))

  id⊸ : ∀ {P : Rel} → P ⊸ P
  id⊸ = (λ▹ vt)

  _≅i_ : (P Q : Rel) → Set
  P ≅i Q = Σ \ (f : P ⊸ Q) →
          Σ \ (g : Q ⊸ P) →
            _==_{_}{P ⊸ P} (f then⊸ g) id⊸
          × _==_{_}{Q ⊸ Q} (g then⊸ f) id⊸

  -- ----------------------------------------------------------------------
  -- morphism types

  postulate 
    mor0  :  Rel 

  postulate
    id0 : vc ⊢ mor0

  ident : vc ⊢ mor0
  ident = id0 

  apply-to-id : (Q : Rel)
              → (mor0 ⊸ Q)
              → vc ⊢ Q
  apply-to-id Q t = (app▹ t (ident))

  postulate
    ind-mor-iso : ∀ Q → isIso _ _ (apply-to-id Q)

  ind-mor :  (Q : Rel )
            → vc ⊢ Q
            → vc ⊢ (mor0 ▹ Q )
  ind-mor Q = isIso.g (ind-mor-iso Q)

  ind-morβ : (Q : Rel )
             (t : vc ⊢ Q)
           →  (app▹ ((ind-mor Q t) ) (ident)) ==  t
  ind-morβ Q t = isIso.fg (ind-mor-iso Q) t

  postulate
    subst-id0 : subst-tr id0 vs == id0

    subst-ind-mor : ∀ Q (t : vc ⊢ Q) → subst-tr (ind-mor Q t) vs == (ind-mor Q t) 

  ind-mor-ext : (Q : Rel ) (t s : mor0 ⊸ Q)
              → apply-to-id Q t == apply-to-id Q s
              → t == s
  ind-mor-ext Q t s p = (isIso.gf (ind-mor-iso Q) _) ∘ ap (ind-mor Q) p ∘ ! (isIso.gf (ind-mor-iso Q) _)

{-
  ind-morη : {ℂ 𝔻 : Cat} (Q : Rel ℂ ℂ)
             (t : ∀e {ℂ} (mor ℂ v v ▹ Q ))
           → t == ind-mor Q (λe (app▹ (appe t v) v (ident v) ))
  ind-morη Q  t = ! (isIso.gf (ind-mor-iso Q) t)
-}

{-
  -- ----------------------------------------------------------------------
  -- tensor types

  postulate
    _⊙_  : ∀ {ℂ  𝔻 𝔼 : Cat} (P : Rel ℂ 𝔼) (Q : Rel 𝔼 𝔻) → Rel ℂ 𝔻

  postulate
    ⊙i* : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} → ([ P ] ,, [ Q ]) ⊢ (P ⊙ Q)

  ⊙i : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {ϕ1 : Ctx ℂ 𝔼 } {ϕ2 : Ctx 𝔼 𝔻 } 
     → ϕ1 ⊢ P
     → ϕ2 ⊢ Q
     → (ϕ1 ,, ϕ2) ⊢ (P ⊙ Q)
  ⊙i t s = ⊙i* [ ,,s { c = v} v {e = v} [ t ]s  [ s ]s ]tr

    -- ind-⊙η 
           
  apply-to-pair : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
          → ((P ⊙ Q) ⊸ R)
          → (P ⊸ (Q ▹ R))
  apply-to-pair t = λe (λ▹ (λ▹ (app▹ (appe t v) v ⊙i*)))

  postulate 
    ind-⊙-iso : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
              → isIso _ _ (apply-to-pair {P = P} {Q} {R})

  ind-⊙ : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
          → (P ⊸ (Q ▹ R))
          → ((P ⊙ Q) ⊸ R)
  ind-⊙ t = isIso.g ind-⊙-iso t

  ind-⊙β : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
             (s : (P ⊸ (Q ▹ R)))
           → _==_{_}{∀e {ℂ} (P ▹ (Q ▹ R))} (λe (λ▹ (λ▹ (app▹ (appe (ind-⊙ s) v) v ⊙i*)))) s
  ind-⊙β s = isIso.fg ind-⊙-iso s

  {-# REWRITE ind-⊙β #-}

{-
  ind-⊙η : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
             (s : ((P ⊙ Q) ⊸ R))
           → _==_{_}{∀e {ℂ} ((P ⊙ Q) ▹ R)} (ind-⊙ (apply-to-pair s)) s
  ind-⊙η s = isIso.gf ind-⊙-iso s

  ⊙⊸ext : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
          (f g : (P ⊙ Q) ⊸ R)
       → apply-to-pair f == apply-to-pair g
       → f == g
  ⊙⊸ext f g p = (ind-⊙η g) ∘ ap (ind-⊙) p ∘ ! (ind-⊙η f) 
-}
-}

  -- ----------------------------------------------------------------------
  -- reductions

  {-# REWRITE fuse #-}
  {-# REWRITE subst-ident #-}
  {-# REWRITE subst-ident-vs #-}

  -- {-# REWRITE ,,s-assoc #-}
  {-# REWRITE ,,s-unitl #-}
  {-# REWRITE ,,s-unitr #-}
  {-# REWRITE comps-unit-l #-}
  {-# REWRITE comps-unit-r #-}
  {-# REWRITE comps-vs #-}
  {-# REWRITE ids-vc #-}
  {-# REWRITE subst-vt #-}

  {-# REWRITE β▹ #-}
  {-# REWRITE app▹subst #-}
  {-# REWRITE app▹subst-unitl #-}
  {-# REWRITE app▹subst-unitr #-}
  {-# REWRITE app▹subst-fun #-}
  {-# REWRITE app▹subst-arg #-}
  {-# REWRITE λ▹subst #-}

  {-# REWRITE ind-morβ #-}

  -- {-# REWRITE subst-id0 #-}
  -- {-# REWRITE subst-ind-mor #-}

  {-# REWRITE β◃ #-}
  {-# REWRITE app◃subst #-}
  {-# REWRITE app◃subst-arg #-}
  {-# REWRITE app◃subst-fun #-}
  {-# REWRITE app◃subst-unitr #-}
  {-# REWRITE app◃subst-unitl #-}
  {-# REWRITE λ◃subst #-}
  -- {-# REWRITE λ◃subst #-}



  -- ----------------------------------------------------------------------
  -- examples
  exchange-map : ∀ {P : Rel} {Q : Rel} {R : Rel}
           → (P ⊸ (Q ▹ R))
           → ((Q ⊸ (R ◃ P))) 
  exchange-map t = (λ▹ (λ◃ (app▹ (app▹ t vt) vt)))

  exchange : ∀ {P : Rel} {Q : Rel} {R : Rel}
           → isIso (P ⊸ (Q ▹ R)) ((Q ⊸ (R ◃ P))) exchange-map
  exchange = iso (\ f → λ▹ (λ▹ (app◃ vt (app▹ f vt))) )
                 (\ h → ! (η▹ _) ∘ ap λ▹ (! (η▹ _) ∘ id) )
                 (\ h → ! (η▹ _) ∘ ap λ▹ (! (η◃ _) ∘ id))

  exchange-ext : {P : Rel} {Q : Rel} {R : Rel}
          (f g : (P ⊸ (Q ▹ R)))
       → exchange-map f == exchange-map g
       → f == g
  exchange-ext f g p = (isIso.gf exchange _) ∘ ap (isIso.g exchange) p ∘ ! (isIso.gf exchange _) 

  yoneda : ∀ (P : Rel) → (mor0 ▹ P) ≅i P
  yoneda P = (λ▹ ( app▹ vt (ident))) ,
              isIso.g exchange (ind-mor (P ◃ P) (λ◃ vt))  ,
             exchange-ext _ _ (ind-mor-ext _ _ _ id) ,
             id


{-
  ⊙assoc : ∀ {ℂ 𝔻 𝔼 𝔽} → (P : Rel ℂ 𝔻) (Q : Rel 𝔻 𝔼) (R : Rel 𝔼 𝔽)
         → ((P ⊙ Q) ⊙ R) ≅i (P ⊙ (Q ⊙ R))
  ⊙assoc P Q R = to ,
                (from ,
                ⊙⊸ext _ _ (⊙⊸ext _ _ {!!}) ,
                ⊙⊸ext _ _ ((exchange-ext _ _ (⊙⊸ext _ _ {!!})))) where
     to-matched : ∀e (P ▹ (Q ▹ (R ▹ (P ⊙ (Q ⊙ R)))))
     to-matched = λe (λ▹ (λ▹ (λ▹ ((transport ( \ H → H ⊢ (P ⊙ (Q ⊙ R))) id -- (! (cassoc [ P ] [ Q ] [ R ])) -- wouldn't be there if contexts were strictly associative
                                              (⊙i {ϕ1 = [ P ]  } {ϕ2 = [ Q ] ,, [ R ]}
                                                  vt
                                                  ⊙i* )))) ))

     to = ind-⊙ (ind-⊙ to-matched)

     from-matched : ∀e (Q ▹ (R ▹ (((P ⊙ Q) ⊙ R) ◃ P)))
     from-matched = λe (λ▹ (λ▹ (λ◃ (transport ( \ H → H ⊢ ((P ⊙ Q) ⊙ R)) id -- (cassoc [ P ] [ Q ] [ R ]) -- wouldn't be there if contexts were strictly associative
                                              (⊙i {ϕ1 = [ P ] ,, [ Q ] } {ϕ2 = [ R ]}
                                                  ⊙i*
                                                  vt )))))
  
     from =  ind-⊙ (isIso.g exchange (ind-⊙ from-matched)) 
     -- (λe (λ▹ (λ▹ (unλ◃ {ϕ = [ Q ⊙ R ]} (unλ⊸ (ind-⊙ from-matched) )))))
                 
  




-}
