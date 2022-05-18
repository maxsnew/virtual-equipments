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
    _·_ : ∀ {ℂ 𝔻 C} → Fun 𝔻 C → Fun ℂ 𝔻 → Fun ℂ C
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
    -- FIXME: preserves composition 

  -- this may be a bad idea... overlaps with the rules pushing in to the type constructors
  {-# REWRITE restrict-id #-}


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
  -- {-# REWRITE cassoc #-}

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
    _[_]tr : ∀ {ℂ 𝔻 ℂ' 𝔻' }
              {ϕ : Ctx ℂ 𝔻}
              {Ψ : Ctx ℂ' 𝔻'}
              {R : Rel ℂ' 𝔻'}
              {c : Fun ℂ ℂ'}
              {d : Fun 𝔻 𝔻'} 
           →  Ψ ⊢ R
           →  ϕ ⊢s Ψ [ c ∣ d ]
           →  ϕ ⊢ R [ c ∣ d ]

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
       → app▹ (λ▹ s) a t == ( s [ ,,s v ids ([ t ]s) ]tr)
    η▹ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼}
       → (f : ϕ ⊢ (R ▹ P))
       → f == λ▹ (app▹ {ϕf = ϕ} {ϕa = [ R ]} f v vt )
    ▹subst : ∀ {ℂ' 𝔻' ℂ 𝔻 𝔼 : Cat} (R : Rel 𝔻 𝔼) (P : Rel ℂ 𝔼)
               → (f : Fun ℂ' ℂ) (g : Fun 𝔻' 𝔻)
           → ( (R ▹ P) ) [ f ∣ g ] == ((R [ g ∣ v ]) ▹ (P [ f ∣ v ]))
  {-# REWRITE ▹subst #-}
  {-# REWRITE β▹ #-}

  postulate
    _◃_  : ∀ {ℂ 𝔻 𝔼 : Cat} (R : Rel 𝔼 ℂ) (P : Rel 𝔼 𝔻) → Rel ℂ 𝔻
    λ◃ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx 𝔻 𝔼} {R : Rel ℂ 𝔻} {P : Rel ℂ 𝔼}
       → ([ R ] ,, ϕ) ⊢ P
       → ϕ ⊢ (R ◃ P)
    app◃ : {ℂ 𝔻 𝔼 𝔼' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔼 ℂ} {P : Rel 𝔼 𝔻} {ϕa : Ctx 𝔼' ℂ}
           (a : Fun 𝔼' 𝔼)
           (t : ϕa ⊢ (R [ a ∣ v ]))
           (s : ϕf ⊢ (R ◃ P))
           → (ϕa ,, ϕf) ⊢ (P [ a ∣ v ])
    -- FIXME: 
    -- β◃ : {ℂ 𝔻 𝔼 𝔼' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
    --        (s : (ϕf ,, [ R ]) ⊢ P)
    --        (a : Fun 𝔼' 𝔼)
    --        (t : ϕa ⊢ (R [ v ∣ a ]))
    --    → app◃ (λ◃ s) a t == ( s [ ,,s v ids ([ t ]s) ]tr)
    -- η◃ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx ℂ 𝔻} {R : Rel 𝔻 𝔼} {P : Rel ℂ 𝔼}
    --    → (f : ϕ ⊢ (R ◃ P))
    --    → f == λ◃ (app◃ {ϕf = ϕ} {ϕa = [ R ]} f v vt )

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

  postulate
    ind-mor : {ℂ : Cat} (Q : Rel ℂ ℂ)
            → ∀e Q
            → ∀e {ℂ} (mor ℂ v v ▹ Q )
    ind-morβ : {ℂ 𝔻 : Cat} (Q : Rel ℂ ℂ)
             (N : ∀e Q)
             →  λe (app▹ (appe (ind-mor Q N) v ) v (ident v)) ==  N
    ind-morη : {ℂ 𝔻 : Cat} (Q : Rel ℂ ℂ)
               (N : ∀e {ℂ} (mor ℂ v v ▹ Q ))
             → N == ind-mor Q (λe (app▹ (appe N v) v (ident v) )) 

  -- FIXME does this need some more naturality?

  -- ----------------------------------------------------------------------
  -- tensor types

  postulate
    _⊙_  : ∀ {ℂ  𝔻 𝔼 : Cat} (P : Rel ℂ 𝔼) (Q : Rel 𝔼 𝔻) → Rel ℂ 𝔻

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

  
