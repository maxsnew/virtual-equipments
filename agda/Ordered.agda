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
    ,,s-assoc  : ∀ 
                 {ϕ1 : Ctx} {ϕ2 : Ctx} {ϕ3 : Ctx}
                 {Ψ1 : Ctx} {Ψ2 : Ctx} {Ψ3 : Ctx}
                 → (f1 : ϕ1 ⊢s Ψ1)
                 → (f2 : ϕ2 ⊢s Ψ2)
                 → (f3 : ϕ3 ⊢s Ψ3)
                 → (,,s (,,s f1 f2) f3) == (,,s f1 (,,s f2 f3))
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

    ids-,, : ∀ {ϕ1 ϕ2} → ids {ϕ1 ,, ϕ2} == (,,s (ids{ϕ1}) (ids{ϕ2}))
    ids-[] : ∀ {R} → ids {[ R ]} == [ vt ]s

    comps-unit-r : {ϕ1 : Ctx} {ϕ2 : Ctx}  
          → (s : ϕ1 ⊢s ϕ2)
          → comps s ids == s

    comps-unit-l : {ϕ1 : Ctx} {ϕ2 : Ctx}  
          → (s : ϕ1 ⊢s ϕ2)
          → comps ids s == s

    comps-vs : {ϕ1 : Ctx}
             → (s : ϕ1 ⊢s vc)
             → comps s vs == s

    ,,s-comp : ∀ {ϕ1 : Ctx} {ϕ2 : Ctx}
             {Ψ1 : Ctx} {Ψ2 : Ctx}
             {Ξ1 : Ctx} {Ξ2 : Ctx}
             (s1 : ϕ1 ⊢s Ψ1)
             (s2 : ϕ2 ⊢s Ψ2)
             (t1 : Ξ1 ⊢s ϕ1)
             (t2 : Ξ2 ⊢s ϕ2)
           → (comps (,,s t1 t2) (,,s s1 s2)) == (,,s (comps t1 s1) (comps t2 s2))

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

      comps-[] : {ϕ1 : Ctx} {ϕ2 : Ctx}  {R : Rel}
               → (t : ϕ1 ⊢s ϕ2 )
               → (s : ϕ2 ⊢ R )
               → comps t [ s ]s == [ subst-tr s t ]s
          

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

    app▹subst-lassoc-ctx : {ϕf  : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
                (s : ϕf ⊢ (R ▹ P))
                (t : ϕa ⊢ (R))
              → {ϕf' ϕf'' : Ctx } {ϕa' : Ctx }
              → (ϕ1 : (ϕf' ,, ϕf'') ⊢s ϕf )
              → (ϕ2 : ϕa' ⊢s ϕa )
              → _==_ {_}{(ϕf' ,, (ϕf'' ,, ϕa')) ⊢ (P)}
                     (subst-tr (app▹ s t) (,,s ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (t [ ϕ2 ]tr)) )

    app▹subst-lassoc-subst : {ϕf ϕf2 : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
                (s : (ϕf ,, ϕf2) ⊢ (R ▹ P))
                (t : ϕa ⊢ (R))
              → {ϕf' ϕf2' : Ctx } {ϕa' : Ctx }
              → (ϕ1 : ϕf' ⊢s ϕf )
              → (ϕ2 : ϕf2' ⊢s ϕf2 )
              → (ϕ3 : ϕa' ⊢s ϕa )
              → _==_ {_}{(ϕf' ,, (ϕf2' ,, ϕa')) ⊢ (P)}
                     (subst-tr (app▹ s t) (,,s ϕ1 (,,s ϕ2 ϕ3)))
                     ( (app▹ (s [ ,,s ϕ1 ϕ2 ]tr) (t [ ϕ3 ]tr)) )


  -- not sure why adding these specifically as rewrites helps -- they are just uses of the above
  -- so *should* be implied by them?

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

    app◃subst-lassoc-ctx : {ϕf  : Ctx} {R : Rel} {P : Rel} {ϕa : Ctx}
                (s : ϕf ⊢ (R ◃ P))
                (t : ϕa ⊢ (P))
              → {ϕa' ϕa'' : Ctx } {ϕf' : Ctx }
              → (ϕ1 : (ϕa' ,, ϕa'') ⊢s ϕa )
              → (ϕ2 : ϕf' ⊢s ϕf )
              → _==_ {_}{(ϕa' ,, (ϕa'' ,, ϕf')) ⊢ (R)}
                     (subst-tr (app◃ t s) (,,s ϕ1 ϕ2))
                     ( (app◃ (t [ ϕ1 ]tr) (s [ ϕ2 ]tr)) )

    app◃subst-lassoc-subst : {ϕf : Ctx} {R : Rel} {P : Rel} {ϕa ϕa2 : Ctx}
                (s : ϕf ⊢ (R ◃ P))
                (t : (ϕa ,, ϕa2) ⊢ (P))
              → {ϕf' : Ctx } {ϕa' ϕa2' : Ctx }
              → (ϕ1 : ϕa' ⊢s ϕa )
              → (ϕ2 : ϕa2' ⊢s ϕa2 )
              → (ϕ3 : ϕf' ⊢s ϕf )
              → _==_ {_}
                     (subst-tr (app◃ t s) (,,s ϕ1 (,,s ϕ2 ϕ3)))
                     ( (app◃ (t [ ,,s ϕ1 ϕ2 ]tr) (s [ ϕ3 ]tr)) )


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

  -- ----------------------------------------------------------------------
  -- tensor types

  postulate
    _⊙_  : (P : Rel) (Q : Rel) → Rel

  postulate
    ⊙i* : ∀ {P : Rel} {Q : Rel} → vc ⊢ (P ▹ (Q ▹ (P ⊙ Q)))

  ⊙i : ∀ {P : Rel} {Q : Rel} {ϕ1 : Ctx } {ϕ2 : Ctx } 
     → ϕ1 ⊢ P
     → ϕ2 ⊢ Q
     → (ϕ1 ,, ϕ2) ⊢ (P ⊙ Q)
  ⊙i t s = app▹ (app▹ ⊙i* t) s

  apply-to-pair : ∀ {P : Rel} {Q : Rel} {R : Rel}
          → ((P ⊙ Q) ⊸ R)
          → (P ⊸ (Q ▹ R))
  apply-to-pair t = (λ▹ (λ▹ (app▹ t (⊙i vt vt))))

  postulate 
    ind-⊙-iso : ∀ {P : Rel} {Q : Rel} {R : Rel}
              → isIso _ _ (apply-to-pair {P = P} {Q} {R})

  ind-⊙ : ∀ {P : Rel} {Q : Rel} {R : Rel}
          → (P ⊸ (Q ▹ R))
          → ((P ⊙ Q) ⊸ R)
  ind-⊙ t = isIso.g ind-⊙-iso t

  ind-⊙β : ∀ {P : Rel} {Q : Rel} {R : Rel}
             (s : (P ⊸ (Q ▹ R)))
           → _==_{_} (λ▹ (λ▹ (app▹ (ind-⊙ s) (⊙i vt vt)))) s
  ind-⊙β s = isIso.fg ind-⊙-iso s

  ind-⊙η : ∀ {P : Rel} {Q : Rel} {R : Rel}
             (s : ((P ⊙ Q) ⊸ R))
           → _==_{_} (ind-⊙ (apply-to-pair s)) s
  ind-⊙η s = isIso.gf ind-⊙-iso s

  ⊙⊸ext : ∀ {P : Rel} {Q : Rel} {R : Rel}
          (f g : (P ⊙ Q) ⊸ R)
       → apply-to-pair f == apply-to-pair g
       → f == g
  ⊙⊸ext f g p = (ind-⊙η g) ∘ ap (ind-⊙) p ∘ ! (ind-⊙η f) 

  -- ----------------------------------------------------------------------
  -- reductions

  {-# REWRITE fuse #-}
  {-# REWRITE subst-ident #-}
  {-# REWRITE subst-ident-vs #-}

  {-# REWRITE ,,s-assoc #-}
  {-# REWRITE ,,s-unitl #-}
  {-# REWRITE ,,s-unitr #-}
  {-# REWRITE comps-unit-l #-}
  {-# REWRITE comps-unit-r #-}
  {-# REWRITE comps-vs #-}
  {-# REWRITE ids-vc #-}
  {-# REWRITE subst-vt #-}
  {-# REWRITE ,,s-comp #-}
  {-# REWRITE ids-,, #-}
  {-# REWRITE ids-[] #-}
  {-# REWRITE comps-[] #-}

  {-# REWRITE β▹ #-}
  {-# REWRITE app▹subst #-}
  {-# REWRITE app▹subst-unitl #-}
  {-# REWRITE app▹subst-unitr #-}
  {-# REWRITE app▹subst-fun #-}
  {-# REWRITE app▹subst-arg #-}
  {-# REWRITE app▹subst-lassoc-ctx #-}
  {-# REWRITE app▹subst-lassoc-subst #-}
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
  {-# REWRITE app◃subst-lassoc-ctx #-}
  {-# REWRITE app◃subst-lassoc-subst #-}
  {-# REWRITE λ◃subst #-}

  ind-⊙β' : ∀ {P : Rel} {Q : Rel} {R : Rel}
             (s : (P ⊸ (Q ▹ R)))
             {ϕ1 ϕ2 : Ctx} → 
             (x : ϕ1 ⊢ P)
             (y : ϕ2 ⊢ Q)
           → _==_ {_}{(ϕ1 ,, ϕ2) ⊢ R}
                  (app▹ (isIso.g ind-⊙-iso s) (app▹ (app▹ ⊙i* x) y))
                  (app▹ (app▹ s x) y)
  ind-⊙β' s x y =  ap (\ H → (app▹ (app▹ H x) y)) (ind-⊙β s)

  ind-⊙β'-unitr : ∀ {P : Rel} {Q : Rel} {R : Rel}
             (s : (P ⊸ (Q ▹ R)))
             {ϕ1 : Ctx} → 
             (x : ϕ1 ⊢ P)
             (y : vc ⊢ Q)
           → _==_ {_}{(ϕ1) ⊢ R} (app▹ (isIso.g ind-⊙-iso s) (app▹ (app▹ ⊙i* x) y)) (app▹ (app▹ s x) y)
  ind-⊙β'-unitr s x y =   ind-⊙β' s x y

  ind-⊙β'-unitl : ∀ {P : Rel} {Q : Rel} {R : Rel}
             (s : (P ⊸ (Q ▹ R)))
             {ϕ2 : Ctx} → 
             (x : vc ⊢ P)
             (y : ϕ2 ⊢ Q)
           → _==_ {_}{(ϕ2) ⊢ R} (app▹ (isIso.g ind-⊙-iso s) (app▹ (app▹ ⊙i* x) y)) (app▹ (app▹ s x) y)
  ind-⊙β'-unitl s x y =  ind-⊙β' s x y

  ind-⊙β'-lassoc : ∀ {P : Rel} {Q : Rel} {R : Rel}
             (s : (P ⊸ (Q ▹ R)))
             {ϕ1 ϕ2 ϕ3 : Ctx} → 
             (x : (ϕ1 ,, ϕ2) ⊢ P)
             (y : ϕ3 ⊢ Q)
           → _==_ {_}{(ϕ1 ,, (ϕ2 ,, ϕ3)) ⊢ R}
                  (app▹ (isIso.g ind-⊙-iso s) (app▹ (app▹ ⊙i* x) y))
                  (app▹ (app▹ s x) y)
  ind-⊙β'-lassoc s x y =  ind-⊙β' s x y

  {-# REWRITE ind-⊙β' #-}
  {-# REWRITE ind-⊙β'-unitl #-}
  {-# REWRITE ind-⊙β'-unitr #-}
  {-# REWRITE ind-⊙β'-lassoc #-}


  -- ----------------------------------------------------------------------
  -- examples
  exchange-map : ∀ {P : Rel} {Q : Rel} {R : Rel}
           → (P ⊸ (Q ▹ R))
           → ((Q ⊸ (R ◃ P))) 
  exchange-map t = (λ▹ (λ◃ (app▹ (app▹ t vt) vt)))

  exchange : ∀ {P : Rel} {Q : Rel} {R : Rel}
           → isIso (P ⊸ (Q ▹ R)) ((Q ⊸ (R ◃ P))) exchange-map
  exchange = iso (\ f → λ▹ (λ▹ (app◃ vt (app▹ f vt))) )
                 (\ h →  ! (η▹ h)  ∘  ap λ▹ (! (η▹ (app▹ h vt)))   )
                 (\ h → ! (η▹ _) ∘ ap λ▹ (! (η◃ _)))

  yoneda-r : ∀ (P : Rel) → (mor0 ▹ P) ≅i P
  yoneda-r P = (λ▹ ( app▹ vt (ident))) ,
             isIso.g exchange (ind-mor (P ◃ P) (λ◃ vt))  ,
             induct-iso-lr exchange (ind-mor-ext _ _ _ id) ,
             id

  yoneda-l : ∀ (P : Rel) → (P ◃ mor0 ) ≅i P
  yoneda-l P = λ▹ (app◃ ident vt) ,
               exchange-map (ind-mor _ (λ▹ vt)) ,
               induct-iso-rl exchange (ind-mor-ext _ _ _ id) ,
               id

  coyoneda-l : ∀ (P : Rel) → (mor0 ⊙ P) ≅i P
  coyoneda-l P = ind-⊙ (ind-mor _ (λ▹ vt)) ,
                 λ▹ (⊙i ident vt) ,
                 (⊙⊸ext _ _ (ind-mor-ext _ _ _ id)) ,
                 id

  coyoneda-r : ∀ (P : Rel) → (P ⊙ mor0) ≅i P
  coyoneda-r P = ind-⊙ (isIso.g exchange (ind-mor _ (λ◃ vt))) ,
                 λ▹ (⊙i vt ident) ,
                 ⊙⊸ext _ _ (induct-iso-lr exchange (ind-mor-ext _ _ _ id)) ,
                 id

  fubini1 : ∀ {P Q R} → ((P ⊙ Q) ⊙ R) ≅i (P ⊙ (Q ⊙ R))
  fubini1 {P}{Q}{R} = ind-⊙ (ind-⊙ (λ▹ (λ▹ (λ▹ (⊙i vt (⊙i vt vt)))))) ,
            ind-⊙ (isIso.g exchange (ind-⊙ (λ▹ (λ▹ (λ◃ (⊙i (⊙i vt vt) vt )))))) ,
            ⊙⊸ext _ _ (⊙⊸ext _ _ id) ,
            ⊙⊸ext _ _ (induct-iso-lr exchange (⊙⊸ext _ _ id))

  fubini2 : ∀ {P Q R} → ((P ⊙ Q) ▹ R) ≅i (P ▹ (Q ▹ R))
  fubini2 {P} {Q} {R} = λ▹ (λ▹ (λ▹ (app▹ {ϕf = [ (P ⊙ Q) ▹ R ]} {ϕa = [ P ] ,, [ Q ]} vt (⊙i vt vt)))) ,
                        isIso.g exchange (ind-⊙ (λ▹ (λ▹ (λ◃ (app▹ {ϕa = [ Q ]} (app▹ {ϕf = [ P ▹ (Q ▹ R) ]} {ϕa = [ P ]} vt vt) vt))))) ,
                        induct-iso-lr exchange (⊙⊸ext _ _ id) ,
                        ap λ▹ (! (η▹ _) ∘ ap λ▹ (! (η▹ _)))

  fubini3 : ∀ {P Q R} → (R ◃ (P ⊙ Q)) ≅i ((R ◃ P) ◃ Q)
  fubini3 {P}{Q}{R} = λ▹ (λ◃ (λ◃ (app◃ {ϕa = [ P ] ,, [ Q ]} (⊙i vt vt) vt))) ,
                      (exchange-map (ind-⊙ (λ▹ (λ▹ (λ▹ (app◃ {ϕa = [ P ]} vt (app◃ {ϕa = [ Q ]}{ϕf = [ (R ◃ P) ◃ Q ]} vt vt))))))) ,
                      induct-iso-rl exchange (⊙⊸ext _ _ id) ,
                      ap λ▹ (! (η◃ _) ∘ ap λ◃ (! (η◃ _)))

  fubini4 : ∀ {P Q R} → (Q ▹ (R ◃ P)) ≅i ((Q ▹ R) ◃ P)
  fubini4 {P}{Q}{R} = λ▹ (λ◃ (λ▹ (app◃  {ϕa = [ P ]} {ϕf = ([ Q ▹ (R ◃ P) ] ,, [ Q ])} vt (app▹ {ϕf = [ Q ▹ (R ◃ P) ]} {ϕa = [ Q ]} vt vt)))) ,
                      λ▹ (λ▹ (λ◃ (app▹ (app◃ {ϕa = [ P ] } {ϕf = [ (Q ▹ R) ◃ P ]} vt vt) vt))) ,
                      (ap λ▹ (! (η▹ _) ∘ ap λ▹ (! (η◃ _)))) ,
                      (ap λ▹ (! (η◃ _) ∘ ap λ◃ (! (η▹ _))))

  -- external!
  fubini5 : ∀ {P Q : Rel} → Iso (vc ⊢ (P ▹ Q)) (vc ⊢ (Q ◃ P))
  fubini5 = iso (\ t → λ◃ (app▹ t vt)) ((\ t → λ▹ (app◃ vt t))) (\ x → ! (η▹ x)) (\ x → ! (η◃ _))
