{-# OPTIONS --rewriting #-}

open import Lib

module STC where

  infixr 4 _·_ 

  infix 30 _[_∣_]

  -- --------------------------------------------------------------------
  -- "categories"
  
  postulate
    Cat : Set

  -- --------------------------------------------------------------------
  -- "functions"

  postulate
    Fun : Cat → Cat → Set
    v : ∀ {ℂ} → Fun ℂ ℂ
    _·_ : ∀ {ℂ 𝔻 𝔼} → Fun 𝔻 𝔼 → Fun ℂ 𝔻 → Fun ℂ 𝔼
    unitr : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻) → (f · v) == f
    unitl : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻) → (v · f) == f
    assoc : ∀ {ℂ 𝔻 C D} (f : Fun C D) (g : Fun 𝔻 C) (h : Fun ℂ 𝔻)
          → ((f · g) · h) == (f · (g · h))

  {-# REWRITE unitl #-}
  {-# REWRITE unitr #-}
  {-# REWRITE assoc #-}

  -- --------------------------------------------------------------------
  -- "relations"

  postulate 
    Rel : Cat → Cat → Set

    -- simulateous substitution for the two free variables of a relation
    -- note: the bar is \mid
    _[_∣_] : {ℂ 𝔻 ℂ' 𝔻' : Cat} → Rel ℂ 𝔻 → Fun ℂ' ℂ → Fun 𝔻' 𝔻 → Rel ℂ' 𝔻'
    restrict-id : ∀ {ℂ 𝔻} (R : Rel ℂ 𝔻) → R [ v ∣ v ] == R  
    restrict-comp : ∀ {ℂ1 ℂ2 ℂ3 𝔻1 𝔻2 𝔻3} (R : Rel ℂ3 𝔻3)
                    (f : Fun ℂ2 ℂ3) (f' : Fun ℂ1 ℂ2)
                    (g : Fun 𝔻2 𝔻3) (g' : Fun 𝔻1 𝔻2)
                  → (R [ f ∣ g ]) [ f' ∣  g' ] == (R [ f · f' ∣ g · g' ])


  -- this may be a bad idea... overlaps with the rules pushing in to the type constructors
  {-# REWRITE restrict-id #-}
  {-# REWRITE restrict-comp #-}


  -- --------------------------------------------------------------------
  -- "relation contexts" as joinlists

  postulate
    Ctx : Cat → Cat → Set
    [_]    : ∀ {ℂ 𝔻} → Rel ℂ 𝔻 → Ctx ℂ 𝔻
    _,,_   : ∀ {ℂ 𝔻 𝔼} → Ctx ℂ 𝔻 → Ctx 𝔻 𝔼 → Ctx ℂ 𝔼
    vc     : (ℂ : Cat) → Ctx ℂ ℂ
    cunitr : ∀ {ℂ 𝔻} (ϕ : Ctx ℂ 𝔻) → (ϕ ,, vc _) == ϕ
    cunitl : ∀ {ℂ 𝔻} (ϕ : Ctx ℂ 𝔻) → (vc _ ,, ϕ) == ϕ
    cassoc : ∀ {ℂ 𝔻 𝔼 𝔽} (ϕ1 : Ctx ℂ 𝔻) (ϕ2 : Ctx 𝔻 𝔼) (ϕ3 : Ctx 𝔼 𝔽)
           → ((ϕ1 ,, ϕ2) ,, ϕ3) == (ϕ1 ,, (ϕ2 ,, ϕ3))

  {-# REWRITE cunitl #-}
  {-# REWRITE cunitr #-}
  {-# REWRITE cassoc #-}

  -- --------------------------------------------------------------------
  -- transformation terms

  postulate 
    _⊢_ : ∀ {ℂ 𝔻} → Ctx ℂ 𝔻 → Rel ℂ 𝔻 → Set
    vt : ∀ {ℂ 𝔻} {R : Rel ℂ 𝔻} → [ R ] ⊢ R

  -- --------------------------------------------------------------------
  -- transformation substitutions (squares)

  postulate
    _⊢s_[_∣_] : ∀ {ℂ 𝔻 ℂ' 𝔻'} → Ctx ℂ 𝔻 → Ctx ℂ' 𝔻' → Fun ℂ ℂ' → Fun 𝔻 𝔻' → Set
    [_]s   : ∀ {ℂ 𝔻 ℂ' 𝔻'} {ϕ : Ctx ℂ 𝔻} {R : Rel ℂ' 𝔻'}
             {f : Fun ℂ ℂ'}
             {g : Fun 𝔻 𝔻'} 
           → ϕ ⊢ (R [ f ∣ g ])
           → ϕ ⊢s [ R ] [ f ∣ g ]
    vs     : ∀ {ℂ 𝔻} → (f : Fun ℂ 𝔻) → vc ℂ ⊢s vc 𝔻 [ f ∣ f ]
    ,,s  : ∀ {ℂ 𝔻 𝔼 ℂ' 𝔻' 𝔼'}
             {ϕ1 : Ctx ℂ 𝔻} {ϕ2 : Ctx 𝔻 𝔼}
             {Ψ1 : Ctx ℂ' 𝔻'} {Ψ2 : Ctx 𝔻' 𝔼'}
             {c : Fun ℂ ℂ'} (d : Fun 𝔻 𝔻') {e : Fun 𝔼 𝔼'}
           → ϕ1 ⊢s Ψ1 [ c ∣ d ]
           → ϕ2 ⊢s Ψ2 [ d ∣ e ] 
           → (ϕ1 ,, ϕ2) ⊢s (Ψ1 ,, Ψ2) [ c ∣ e ]
    ids   :  ∀ {ℂ 𝔻 } {ϕ : Ctx ℂ 𝔻} → ϕ ⊢s ϕ [ v ∣ v ]
    -- comps : 
    -- TODO associativity, unit, interchange, def id and comp

  -- --------------------------------------------------------------------
  -- substitution into a term

  postulate
    subst-tr : ∀ {ℂ 𝔻 ℂ' 𝔻' }
              {ϕ : Ctx ℂ 𝔻}
              {Ψ : Ctx ℂ' 𝔻'}
              {R : Rel ℂ' 𝔻'}
              {c : Fun ℂ ℂ'}
              {d : Fun 𝔻 𝔻'} 
           →  Ψ ⊢ R
           →  ϕ ⊢s Ψ [ c ∣ d ]
           →  ϕ ⊢ R [ c ∣ d ]

  _[_]tr : ∀ {ℂ 𝔻 ℂ' 𝔻' }
              {ϕ : Ctx ℂ 𝔻}
              {Ψ : Ctx ℂ' 𝔻'}
              {R : Rel ℂ' 𝔻'}
              {c : Fun ℂ ℂ'}
              {d : Fun 𝔻 𝔻'} 
           →  Ψ ⊢ R
           →  ϕ ⊢s Ψ [ c ∣ d ]
           →  ϕ ⊢ R [ c ∣ d ]
  _[_]tr = subst-tr
  

  -- ----------------------------------------------------------------------
  -- end

  postulate
    ∀e : {ℂ : Cat} → Rel ℂ ℂ → Set
    λe : {ℂ : Cat} {R : Rel ℂ ℂ}
       → vc ℂ ⊢ R
       → ∀e R
    appe : {𝔻 ℂ : Cat} {R : Rel ℂ ℂ}
         → ∀e R
         → (f : Fun 𝔻 ℂ)
         → vc 𝔻 ⊢ R [ f ∣ f ]
    ∀eβ : {𝔻 ℂ : Cat} {R : Rel ℂ ℂ}
         → (t : vc ℂ ⊢ R)
         → (c : Fun 𝔻 ℂ)
         → appe (λe t) c == (t [ vs c ]tr)
    ∀eη : {𝔻 ℂ : Cat} {R : Rel ℂ ℂ}
         → (t : ∀e R)
         → (c : Fun 𝔻 ℂ)
         → t == λe (appe t v)

  {-# REWRITE ∀eβ #-}

  -- --------------------------------------------------------------------
  -- hom types 

  postulate
    _▹_  : ∀ {ℂ 𝔻 𝔼 : Cat} (R : Rel 𝔻 𝔼) (P : Rel ℂ 𝔼) → Rel ℂ 𝔻
    λ▹ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼}
       → (ϕ ,, [ R ]) ⊢ P
       → ϕ ⊢ (R ▹ P)
    app▹ : {ℂ 𝔻 𝔼 𝔼' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
           (s : ϕf ⊢ (R ▹ P))
           (a : Fun 𝔼' 𝔼)
           (t : ϕa ⊢ (R [ v ∣ a ]))
           → (ϕf ,, ϕa) ⊢ (P [ v ∣ a ])
    β▹ : {ℂ 𝔻 𝔼 𝔼' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
           (s : (ϕf ,, [ R ]) ⊢ P)
           (a : Fun 𝔼' 𝔼)
           (t : ϕa ⊢ (R [ v ∣ a ]))
       → app▹ {ϕf = ϕf} {ϕa = ϕa} (λ▹ s) a t == ( s [ ,,s {ϕ1 = ϕf} {ϕ2 = ϕa} v ids ([ t ]s) ]tr)
    η▹ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼}
       → (f : ϕ ⊢ (R ▹ P))
       → f == λ▹ (app▹ {ϕf = ϕ} {ϕa = [ R ]} f v vt )
    ▹subst : ∀ {ℂ' 𝔻' ℂ 𝔻 𝔼 : Cat} (R : Rel 𝔻 𝔼) (P : Rel ℂ 𝔼)
               → (f : Fun ℂ' ℂ) (g : Fun 𝔻' 𝔻)
           → ( (R ▹ P) ) [ f ∣ g ] == ((R [ g ∣ v ]) ▹ (P [ f ∣ v ]))
  {-# REWRITE ▹subst #-}
  postulate
    λ▹subst : {ℂ 𝔻 𝔼 ℂ' 𝔻' : Cat} {ϕ : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼}
       → (s : (ϕ ,, [ R ]) ⊢ P)
       → (ϕ' : Ctx ℂ' 𝔻')
       → ∀ {h1 h2}
       → (ϕ0 : ϕ' ⊢s ϕ [ h1 ∣ h2 ])
       → (subst-tr (λ▹ s) ϕ0) == λ▹ (s [ ,,s _ ϕ0 [ vt ]s ]tr) 
       
    app▹subst : {ℂ 𝔻 𝔼 𝔼' ℂ'' 𝔻'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
                (s : ϕf ⊢ (R ▹ P))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (R [ v ∣ a ]))
              → {ϕf' : Ctx ℂ'' 𝔻''} {ϕa' : Ctx 𝔻'' 𝔼''}
              → ∀ {h1 h2 h4}
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ h4 ])
              → _==_ {_}{(ϕf' ,, ϕa') ⊢ (P [ v · h1 ∣ a · h4 ])}
                     (subst-tr (app▹ s a t) (,,s _ ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (a · h4) (t [ ϕ2 ]tr)) )

  app▹subst1 : {ℂ 𝔼 𝔼'' : Cat} {R : Rel ℂ 𝔼} {P : Rel ℂ 𝔼} 
                (s : (vc ℂ) ⊢ (R ▹ P))
                (a : Fun ℂ 𝔼 )
                (t : (vc ℂ) ⊢ (R [ v ∣ a ]))
              → ∀ {h4 : Fun 𝔼'' ℂ}
              → _==_ {_}
                     (subst-tr (app▹ s a t) (vs h4))
                     ( (app▹ (s [ vs h4 ]tr) (a · h4) (t [ vs h4 ]tr)) )
  app▹subst1 s a t {h4} = app▹subst s a t (vs h4) (vs h4) ∘ {!!}

  {-# REWRITE β▹ #-}
  {-# REWRITE app▹subst #-}
  {-# REWRITE λ▹subst #-}
  -- {-# REWRITE app▹subst1 #-}

  postulate
    _◃_  : ∀ {ℂ 𝔻 𝔼 : Cat} (R : Rel 𝔼 𝔻) (P : Rel 𝔼 ℂ) → Rel ℂ 𝔻
    λ◃ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx ℂ 𝔻} {R : Rel 𝔼 𝔻} {P : Rel 𝔼 ℂ}
       → ([ P ] ,, ϕ) ⊢ R
       → ϕ ⊢ (R ◃ P)
    app◃ : {ℂ 𝔻 𝔼 𝔼' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔼 𝔻} {P : Rel 𝔼 ℂ} {ϕa : Ctx 𝔼' ℂ}
           (a : Fun 𝔼' 𝔼)
           (t : ϕa ⊢ (P [ a ∣ v ]))
           (s : ϕf ⊢ (R ◃ P))
           → (ϕa ,, ϕf) ⊢ (R [ a ∣ v ])
    -- ◃β : {ℂ 𝔻 𝔼 𝔼' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔼 ℂ} {P : Rel 𝔼 𝔻} {ϕa : Ctx 𝔼' ℂ}
    --      (a : Fun 𝔼' 𝔼)
    --      (t : ϕa ⊢ (R [ a ∣ v ]))
    --      (s : ([ R ] ,, ϕf) ⊢ P)
    --     → app◃ a t (λ◃ s) == (s [ ,,s v [ t ]s ids ]tr)
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

  -- ----------------------------------------------------------------------
  -- n.t. of profunctors
  
  _⊸_ : ∀ {ℂ 𝔻} (P Q : Rel ℂ 𝔻) → Set
  P ⊸ Q = ∀e (P ▹ Q)

  unλ⊸ : ∀ {ℂ 𝔻} {P Q : Rel ℂ 𝔻}
          → P ⊸ Q
          → [ P ] ⊢ Q
  unλ⊸ f = app▹ (appe f v) v vt

  _then⊸_ : ∀ {ℂ 𝔻} {P Q R : Rel ℂ 𝔻}
          → P ⊸ Q
          → Q ⊸ R
          → P ⊸ R
  f then⊸ g = λe (λ▹ (app▹ (appe g v) v (app▹ (appe f v) v vt) ))

  id⊸ : ∀ {ℂ 𝔻} {P : Rel ℂ 𝔻} → P ⊸ P
  id⊸ = λe (λ▹ vt)

  _≅i_ : ∀ {ℂ 𝔻} (P Q : Rel ℂ 𝔻) → Set
  P ≅i Q = Σ \ (f : P ⊸ Q) →
          Σ \ (g : Q ⊸ P) →
            _==_{_}{P ⊸ P} (f then⊸ g) id⊸
          × _==_{_}{Q ⊸ Q} (g then⊸ f) id⊸


  -- ----------------------------------------------------------------------
  -- morphism types

  postulate 
    mor0  : {ℂ : Cat} → Rel ℂ ℂ

  mor  : ∀ {ℂ 𝔻 : Cat} → (𝔼 : Cat) (f : Fun ℂ 𝔼) (g : Fun 𝔻 𝔼) → Rel ℂ 𝔻
  mor 𝔼 f g = mor0 [ f ∣ g ]

  postulate
    id0 : {ℂ : Cat} → ∀e {ℂ} mor0

  ident : {𝔼 ℂ : Cat} (f : Fun 𝔼 ℂ) → vc 𝔼 ⊢ mor ℂ f f
  ident f = appe id0 f

  apply-to-id : {ℂ : Cat} (Q : Rel ℂ ℂ)
              → (mor ℂ v v ⊸ Q)
              → ∀e Q
  apply-to-id Q t = λe (app▹ (appe t v) v (ident v))

  postulate
    ind-mor-iso : {ℂ : Cat} (Q : Rel ℂ ℂ) → isIso _ _ (apply-to-id Q)

  ind-mor : {ℂ : Cat} (Q : Rel ℂ ℂ)
            → ∀e Q
            → ∀e {ℂ} (mor ℂ v v ▹ Q )
  ind-mor Q = isIso.g (ind-mor-iso Q)

  ind-morβ : {ℂ 𝔻 : Cat} (Q : Rel ℂ ℂ)
             (t : ∀e Q)
           →  λe (app▹ (appe (ind-mor Q t) v ) v (ident v)) ==  t
  ind-morβ Q t = isIso.fg (ind-mor-iso Q) t

  ind-morη : {ℂ 𝔻 : Cat} (Q : Rel ℂ ℂ)
             (t : ∀e {ℂ} (mor ℂ v v ▹ Q ))
           → t == ind-mor Q (λe (app▹ (appe t v) v (ident v) ))
  ind-morη Q  t = ! (isIso.gf (ind-mor-iso Q) t)

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

  ind-⊙η : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
             (s : ((P ⊙ Q) ⊸ R))
           → _==_{_}{∀e {ℂ} ((P ⊙ Q) ▹ R)} (ind-⊙ (apply-to-pair s)) s
  ind-⊙η s = isIso.gf ind-⊙-iso s

  ⊙⊸ext : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
          (f g : (P ⊙ Q) ⊸ R)
       → apply-to-pair f == apply-to-pair g
       → f == g
  ⊙⊸ext f g p = (ind-⊙η g) ∘ ap (ind-⊙) p ∘ ! (ind-⊙η f) 

  -- ----------------------------------------------------------------------
  -- product categories
  postulate 
    _×c_   : Cat → Cat → Cat
    pair   : ∀{ℂ 𝔻 𝔼} → Fun 𝔼 ℂ → Fun 𝔼 𝔻 → Fun 𝔼 (ℂ ×c 𝔻)
    first  : ∀{ℂ 𝔻 𝔼} → Fun 𝔼 (ℂ ×c 𝔻) → Fun 𝔼 ℂ
    second : ∀{ℂ 𝔻 𝔼} → Fun 𝔼 (ℂ ×c 𝔻) → Fun 𝔼 𝔻
    pairβ1 : ∀{ℂ 𝔻 𝔼} (a : Fun 𝔼 ℂ) (b : Fun 𝔼 𝔻) → first (pair a b) == a
    pairβ2 : ∀{ℂ 𝔻 𝔼} (a : Fun 𝔼 ℂ) (b : Fun 𝔼 𝔻) → second (pair a b) == b
    pairη : ∀{ℂ 𝔻 𝔼} (p : Fun 𝔼 (ℂ ×c 𝔻)) → p == (pair (first p) (second p)) 

  {-# REWRITE pairβ1 #-}
  {-# REWRITE pairβ2 #-}

  -- ----------------------------------------------------------------------
  -- examples
  
  example : ∀ {ℂ 𝔻} → (Fun ℂ 𝔻) → Set 
  example {ℂ}{𝔻} f = ∀e ((mor ℂ v v) ▹ mor 𝔻 (f · v) (f · v))

  exchange-map : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
           → (P ⊸ (Q ▹ R))
           → ((Q ⊸ (R ◃ P)))
  exchange-map t = λe (λ▹ (λ◃ (app▹ (app▹ (appe t v) v vt) v vt)))

  exchange : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
           → isIso (P ⊸ (Q ▹ R)) ((Q ⊸ (R ◃ P))) exchange-map
  exchange = {!!}

  exchange-ext : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
          (f g : (P ⊸ (Q ▹ R)))
       → exchange-map f == exchange-map g
       → f == g
  exchange-ext  = {!!}

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
                 
  


