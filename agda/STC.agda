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

  {-# REWRITE assoc #-}
  {-# REWRITE unitl #-}
  {-# REWRITE unitr #-}

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
    ids   :  ∀ {ℂ 𝔻} {ϕ : Ctx ℂ 𝔻} → ϕ ⊢s ϕ [ v ∣ v ]
{-
    not used in these examples 
    comps : ∀ {ℂ1 𝔻1 ℂ2 𝔻2 ℂ3 𝔻3} {ϕ1 : Ctx ℂ1 𝔻1} {ϕ2 : Ctx ℂ2 𝔻2}  {ϕ3 : Ctx ℂ3 𝔻3}
          → ∀ {f1 g1 f2 g2}
          → ϕ1 ⊢s ϕ2 [ f1 ∣ g1 ]
          → ϕ2 ⊢s ϕ3 [ f2 ∣ g2 ]
          → ϕ1 ⊢s ϕ3 [ f2 · f1 ∣ g2 · g1 ]
-}

    -- ----------------------------------------------------------------------
    -- horizontal associativity and unit 
    ,,s-assoc  : ∀ {ℂ 𝔻 𝔼 ℂ' 𝔻' 𝔼' 𝔽 𝔽'}
                 {ϕ1 : Ctx ℂ 𝔻} {ϕ2 : Ctx 𝔻 𝔼} {ϕ3 : Ctx 𝔼 𝔽}
                 {Ψ1 : Ctx ℂ' 𝔻'} {Ψ2 : Ctx 𝔻' 𝔼'} {Ψ3 : Ctx 𝔼' 𝔽'}
                 {c : Fun ℂ ℂ'} (d : Fun 𝔻 𝔻') {e : Fun 𝔼 𝔼'} {f : Fun 𝔽 𝔽'}
                 → (f1 : ϕ1 ⊢s Ψ1 [ c ∣ d ])
                 → (f2 : ϕ2 ⊢s Ψ2 [ d ∣ e ])
                 → (f3 : ϕ3 ⊢s Ψ3 [ e ∣ f ])
                 → (,,s _ (,,s _ f1 f2) f3) == (,,s _ f1 (,,s _ f2 f3))
    ,,s-unitr  : ∀ {ℂ 𝔻 ℂ' 𝔻' }
             {ϕ1 : Ctx ℂ 𝔻} 
             {Ψ1 : Ctx ℂ' 𝔻'}
             {c : Fun ℂ ℂ'} (d : Fun 𝔻 𝔻') 
           → (f : ϕ1 ⊢s Ψ1 [ c ∣ d ])
           → (,,s d f (vs d)) == f
    ,,s-unitl  : ∀ {ℂ 𝔻 ℂ' 𝔻' }
             {ϕ1 : Ctx ℂ 𝔻} 
             {Ψ1 : Ctx ℂ' 𝔻'}
             {c : Fun ℂ ℂ'} (d : Fun 𝔻 𝔻') 
           → (f : ϕ1 ⊢s Ψ1 [ c ∣ d ])
           → (,,s c (vs c) f) == f

  -- ---------------------------------------------------------------------- 
  -- vertical associativity and unit (not used in these examples)

  -- ----------------------------------------------------------------------
  -- "definition" of identity based on the context 

    ids-vc : {ℂ : Cat} → ids {ℂ} == vs v
  
    ids-,, : ∀ {ℂ 𝔻 𝔼} {ϕ1 : Ctx ℂ 𝔻} {ϕ2 : Ctx 𝔻 𝔼} →
           ids {ϕ = ϕ1 ,, ϕ2} == (,,s v (ids{ϕ = ϕ1}) (ids{ϕ = ϕ2}))

    ids-[] : ∀ {ℂ 𝔻} {R : Rel ℂ 𝔻} → ids {ϕ = [ R ]} == [ vt ]s

  -- ----------------------------------------------------------------------
  -- "definition" of composition based on the substitution being substituted into
  -- (not used in these examples)

  -- unit law for vs
  -- = substitution into term for singleton
  -- interchange for ,,s 

  {-# REWRITE ,,s-assoc #-}
  {-# REWRITE ,,s-unitl #-}
  {-# REWRITE ,,s-unitr #-}
  {-# REWRITE ids-vc #-}
  {-# REWRITE ids-,, #-}
  {-# REWRITE ids-[] #-}
  
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

  {- -- not used here
  postulate
      fuse : ∀ {ℂ1 𝔻1 ℂ2 𝔻2 ℂ3 𝔻3} {ϕ1 : Ctx ℂ1 𝔻1} {ϕ2 : Ctx ℂ2 𝔻2}  {ϕ3 : Ctx ℂ3 𝔻3}
          → (f1 : Fun ℂ1 ℂ2) (g1 : Fun 𝔻1 𝔻2) (f2 : Fun ℂ2 ℂ3) (g2 : Fun 𝔻2 𝔻3)
          → (s1 : ϕ1 ⊢s ϕ2 [ f1 ∣ g1 ])
          → (s2 : ϕ2 ⊢s ϕ3 [ f2 ∣ g2 ])
          → {R : Rel ℂ3 𝔻3}
          → (t : ϕ3 ⊢ R)
          → (subst-tr (subst-tr t s2) s1) == (t [ comps s1 s2 ]tr)
  -}

  postulate
      subst-ident : ∀ {ℂ 𝔻} {ϕ1 : Ctx ℂ 𝔻} {R : Rel ℂ 𝔻} 
                  → (s : ϕ1 ⊢ R )
                  → subst-tr s ids == s

      subst-vt-gen : ∀ {ℂ' 𝔻' ℂ 𝔻} {ϕ1 : Ctx ℂ' 𝔻'} {R : Rel ℂ 𝔻}
                   → ∀ {f g} 
                   → (s : ϕ1 ⊢ R [ f ∣ g ] )
                   → subst-tr { R = R} {c = f} {d = g} vt ([_]s {f = f} {g = g} s) == s

  {-# REWRITE subst-ident #-}
  {-# REWRITE subst-vt-gen #-}

  -- SPECIAL CASE
  subst-ident-vs : ∀ {ℂ} {R : Rel ℂ ℂ} 
                     → (s : vc ℂ ⊢ R )
                     → subst-tr s (vs v) == s
  subst-ident-vs s = subst-ident s

  subst-ident-vt : ∀ {ℂ 𝔻} {R S : Rel ℂ 𝔻} 
                     → (s : [ S ] ⊢ R )
                     → subst-tr s ([_]s {f = v} {g = v} vt) == s
  subst-ident-vt s =  subst-ident s 

  {-# REWRITE subst-ident-vs #-}
  {-# REWRITE subst-ident-vt #-}

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
    ∀eη : {ℂ : Cat} {R : Rel ℂ ℂ}
         → (t : ∀e R)
         → t == λe (appe t v)
    appe-subst : {𝔼 𝔻 ℂ : Cat} {R : Rel ℂ ℂ}
               → (e : ∀e R)
               → (f : Fun 𝔻 ℂ)
               → (h : Fun 𝔼 𝔻 )
               → subst-tr (appe e f) (vs h) == appe e (f · h)

  -- SPECIAL CASE
  appe-subst-v : {𝔼 ℂ : Cat} {R : Rel ℂ ℂ}
               → (e : ∀e R)
               → (h : Fun 𝔼 ℂ )
               → subst-tr (appe e v) (vs h) == appe e h
  appe-subst-v e h = appe-subst e v h

  {-# REWRITE ∀eβ #-}
  {-# REWRITE appe-subst #-}
  {-# REWRITE appe-subst-v #-}

  ∀e-ext : {ℂ : Cat} { Q : Rel ℂ ℂ}
         → {s t : ∀e Q}
         → appe s v == appe t v
         → s == t
  ∀e-ext p = ! (∀eη _) ∘ ap λe p ∘ (∀eη _)

  -- --------------------------------------------------------------------
  -- left hom type

  postulate
    _▹_  : ∀ {ℂ 𝔻 𝔼 : Cat} (R : Rel 𝔻 𝔼) (P : Rel ℂ 𝔼) → Rel ℂ 𝔻
    ▹subst : ∀ {ℂ' 𝔻' ℂ 𝔻 𝔼 : Cat} (R : Rel 𝔻 𝔼) (P : Rel ℂ 𝔼)
               → (f : Fun ℂ' ℂ) (g : Fun 𝔻' 𝔻)
           → ( (R ▹ P) ) [ f ∣ g ] == ((R [ g ∣ v ]) ▹ (P [ f ∣ v ]))

    λ▹ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx ℂ 𝔻} {P : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
       → (ϕ ,, [ P ]) ⊢ R
       → ϕ ⊢ (P ▹ R)
    app▹ : {ℂ 𝔻 𝔼 𝔼' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
           (s : ϕf ⊢ (P ▹ R))
           (a : Fun 𝔼' 𝔼)
           (t : ϕa ⊢ (P [ v ∣ a ]))
           → (ϕf ,, ϕa) ⊢ (R [ v ∣ a ])
    β▹ : {ℂ 𝔻 𝔼 𝔼' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
           (s : (ϕf ,, [ P ]) ⊢ R)
           (a : Fun 𝔼' 𝔼)
           (t : ϕa ⊢ (P [ v ∣ a ]))
       → app▹ {ϕf = ϕf} {ϕa = ϕa} (λ▹ s) a t == ( s [ ,,s {ϕ1 = ϕf} {ϕ2 = ϕa} v ids ([ t ]s) ]tr)
    η▹ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx ℂ 𝔻} {P : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
       → (f : ϕ ⊢ (P ▹ R))
       → f == λ▹ (app▹ {ϕf = ϕ} {ϕa = [ P ]} f v vt )
  {-# REWRITE ▹subst #-}
  postulate
    -- one of these is derivable from the other and β/η
    λ▹subst : {ℂ 𝔻 𝔼 ℂ' 𝔻' : Cat} {ϕ : Ctx ℂ 𝔻} {P : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
       → (s : (ϕ ,, [ P ]) ⊢ R)
       → (ϕ' : Ctx ℂ' 𝔻')
       → ∀ {h1 h2}
       → (ϕ0 : ϕ' ⊢s ϕ [ h1 ∣ h2 ])
       → (subst-tr (λ▹ s) ϕ0) == λ▹ (s [ ,,s _ ϕ0 [ vt ]s ]tr) 
       
    app▹subst : {ℂ 𝔻 𝔼 𝔼' ℂ'' 𝔻'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼} {ϕa : Ctx 𝔻 𝔼'}
                (s : ϕf ⊢ (P ▹ R))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (P [ v ∣ a ]))
              → {ϕf' : Ctx ℂ'' 𝔻''} {ϕa' : Ctx 𝔻'' 𝔼''}
              → ∀ {h1 h2 h4}
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → (ϕ2 : ϕa' ⊢s ϕa [ h2 ∣ h4 ])
              → _==_ {_}{(ϕf' ,, ϕa') ⊢ (R [ h1 ∣ a · h4 ])}
                     (subst-tr (app▹ s a t) (,,s _ ϕ1 ϕ2))
                     ( (app▹ (s [ ϕ1 ]tr) (a · h4) (t [ ϕ2 ]tr)) )
  {-# REWRITE β▹ #-}
  {-# REWRITE app▹subst #-}
  {-# REWRITE λ▹subst #-}
  
  -- ----------------------------------------------------------------------
  -- right hom type

  postulate
    _◃_  : ∀ {ℂ 𝔻 𝔼 : Cat} (R : Rel 𝔼 𝔻) (P : Rel 𝔼 ℂ) → Rel ℂ 𝔻
    ◃subst : ∀ {ℂ' 𝔻' ℂ 𝔻 𝔼 : Cat} (R : Rel 𝔼 𝔻) (P : Rel 𝔼 ℂ)
               → (f : Fun ℂ' ℂ) (g : Fun 𝔻' 𝔻)
           → ( (R ◃ P) ) [ f ∣ g ] == ((R [ v ∣ g ]) ◃ (P [ v ∣ f ]))

    λ◃ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx ℂ 𝔻} {R : Rel 𝔼 𝔻} {P : Rel 𝔼 ℂ}
       → ([ P ] ,, ϕ) ⊢ R
       → ϕ ⊢ (R ◃ P)
    app◃ : {ℂ 𝔻 𝔼 𝔼' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔼 𝔻} {P : Rel 𝔼 ℂ} {ϕa : Ctx 𝔼' ℂ}
           (a : Fun 𝔼' 𝔼)
           (t : ϕa ⊢ (P [ a ∣ v ]))
           (s : ϕf ⊢ (R ◃ P))
           → (ϕa ,, ϕf) ⊢ (R [ a ∣ v ])
    ◃β : {ℂ 𝔻 𝔼 𝔼' : Cat} {ϕf : Ctx ℂ 𝔻} {R : Rel 𝔼 ℂ} {P : Rel 𝔼 𝔻} {ϕa : Ctx 𝔼' ℂ}
         (a : Fun 𝔼' 𝔼)
         (t : ϕa ⊢ (R [ a ∣ v ]))
         (s : ([ R ] ,, ϕf) ⊢ P)
        → app◃ a t (λ◃ s) == (s [ ,,s v [ t ]s ids ]tr)
    η◃ : {ℂ 𝔻 𝔼 : Cat} {ϕ : Ctx ℂ 𝔻} {R : Rel 𝔼 𝔻} {P : Rel 𝔼 ℂ}
        → (f : ϕ ⊢ (R ◃ P))
        → f == λ◃ (app◃ v vt f )

  {-# REWRITE ◃subst #-}
  {-# REWRITE ◃β #-}

  postulate
      λ◃subst : {ℂ 𝔻 𝔼 ℂ' 𝔻' : Cat} {ϕ : Ctx ℂ 𝔻} {P : Rel 𝔼 ℂ} {R : Rel 𝔼 𝔻}
       → (s : ([ P ] ,, ϕ) ⊢ R)
       → (ϕ' : Ctx ℂ' 𝔻')
       → ∀ {h1 h2}
       → (ϕ0 : ϕ' ⊢s ϕ [ h1 ∣ h2 ])
       → (subst-tr (λ◃ s) ϕ0) == λ◃ (s [ ,,s _ [ vt ]s ϕ0  ]tr) 
      app◃subst : {ℂ 𝔻 𝔼 𝔼' ℂ'' 𝔻'' 𝔼'' : Cat} {ϕf : Ctx ℂ 𝔻} {P : Rel 𝔼 ℂ} {R : Rel 𝔼 𝔻} {ϕa : Ctx 𝔼' ℂ}
                (s : ϕf ⊢ (R ◃ P))
                (a : Fun 𝔼' 𝔼)
                (t : ϕa ⊢ (P [ a ∣ v ]))
              → {ϕf' : Ctx ℂ'' 𝔻''} {ϕa' : Ctx 𝔼'' ℂ''}
              → ∀ {h1 h2 h4}
              → (ϕ1 : ϕf' ⊢s ϕf [ h1 ∣ h2 ])
              → (ϕ2 : ϕa' ⊢s ϕa [ h4 ∣ h1 ])
              → _==_ {_}{(ϕa' ,, ϕf') ⊢ (R [ a · h4 ∣ v · h2 ])}
                     (subst-tr (app◃ a t s) (,,s _ ϕ2 ϕ1))
                     ( (app◃ (a · h4) (t [ ϕ2 ]tr) (s [ ϕ1 ]tr)) )

  {-# REWRITE λ◃subst #-}
  {-# REWRITE app◃subst #-}

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
    mor-rec-iso : {ℂ : Cat} (Q : Rel ℂ ℂ) → isIso _ _ (apply-to-id Q)

  mor-rec : {ℂ : Cat} (Q : Rel ℂ ℂ)
            → ∀e Q
            → ∀e {ℂ} (mor ℂ v v ▹ Q )
  mor-rec Q = isIso.g (mor-rec-iso Q)

  mor-recβ : {ℂ : Cat} (Q : Rel ℂ ℂ)
             (t : ∀e Q)
           →  λe (app▹ (appe (mor-rec Q t) v ) v (ident v)) ==  t
  mor-recβ Q t = isIso.fg (mor-rec-iso Q) t

  -- better one is activated in SubstitutionRewrites
  -- {-# REWRITE mor-recβ #-}

  mor-ext : ∀ {ℂ} {Q : Rel ℂ ℂ} {t s : mor0 ⊸ Q}
          → apply-to-id Q t == apply-to-id Q s
          → t == s
  mor-ext = induct-iso-lr (mor-rec-iso _) 

  -- ----------------------------------------------------------------------
  -- tensor types

  postulate
    _⊙_  : ∀ {ℂ  𝔻 𝔼 : Cat} (P : Rel ℂ 𝔼) (Q : Rel 𝔼 𝔻) → Rel ℂ 𝔻
    ⊙subst : ∀ {ℂ' 𝔻' ℂ 𝔻 𝔼 : Cat} (P : Rel ℂ 𝔼) (Q : Rel 𝔼 𝔻)
           → (f : Fun ℂ' ℂ) (g : Fun 𝔻' 𝔻)
           → ( (P ⊙ Q) ) [ f ∣ g ] == ((P [ f ∣ v ]) ⊙ (Q [ v ∣ g ]))

  {-# REWRITE ⊙subst #-}

  postulate
    ⊙i* : ∀ {ℂ 𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} → ∀e (P ▹ (Q ▹ (P ⊙ Q)))
    -- x : ℂ, a : P(x,y), y : 𝔻, b : Q(y,z), z : 𝔼 ⊢ ⊙i*(a,y,b) : P (x,y) ⊙y Q(y,z)

  pair⊙ : ∀ {ℂ 𝔻 𝔼' 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {ϕ1 : Ctx ℂ 𝔼' } {ϕ2 : Ctx 𝔼' 𝔻 } 
          (e : Fun 𝔼' 𝔼)
          → ϕ1 ⊢ P [ v ∣ e ]
          → ϕ2 ⊢ Q [ e ∣ v ]
          → (ϕ1 ,, ϕ2) ⊢ (P ⊙ Q)
  pair⊙ e t s = app▹ (app▹ (appe ⊙i* v) e t) v s 

  apply-to-pair : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
          → ((P ⊙ Q) ⊸ R)
          → (P ⊸ (Q ▹ R))
  apply-to-pair t = λe (λ▹ (λ▹ (app▹ (appe t v) v (pair⊙ v vt vt ))))

  postulate 
    ⊙-rec-iso : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
              → isIso _ _ (apply-to-pair {P = P} {Q} {R})

  ⊙-rec : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
          → (P ⊸ (Q ▹ R))
          → ((P ⊙ Q) ⊸ R)
  ⊙-rec t = isIso.g ⊙-rec-iso t

  ⊙-recβ : ∀ {ℂ  𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} {R : Rel ℂ 𝔻}
             (s : (P ⊸ (Q ▹ R)))
           → _==_{_}{∀e {ℂ} (P ▹ (Q ▹ R))} (λe (λ▹ (λ▹ (app▹ (appe (⊙-rec s) v) v (pair⊙ v vt vt))))) s
  ⊙-recβ s = isIso.fg ⊙-rec-iso s

  -- applied one activated later
  -- {-# REWRITE ⊙-recβ #-}

  postulate
    naturality? : ∀ {ℂ 𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} 
           → ∀ {ℂ' 𝔻' 𝔼' f1 f2 f3}
               {ϕ1 : Ctx ℂ' 𝔻'}  {ϕ2 : Ctx 𝔻' 𝔼'}  
               (x : ϕ1 ⊢ P [ f1 ∣ f2 ])
               (y : ϕ2 ⊢ Q [ f2 ∣ f3 ])
          → _==_{_}{ (ϕ1 ,, ϕ2) ⊢ (P ⊙ Q) [ f1 ∣ f3 ]}
                (app▹ (app▹ (appe (⊙i* {P = P [ f1 ∣ v ]} {Q = Q [ v ∣ f3 ]}) v) f2 x) v y)
                (app▹ (app▹ (appe (⊙i* {P = P} {Q = Q}) f1) f2 x) f3 y )

  ⊙-ext : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
          {f g : (P ⊙ Q) ⊸ R}
       → apply-to-pair f == apply-to-pair g
       → f == g
  ⊙-ext p = induct-iso-lr ⊙-rec-iso p

  -- ----------------------------------------------------------------------
  -- product categories
  postulate
    1c : Cat
    empty : ∀ {ℂ} → Fun ℂ 1c
    1η    : ∀ {ℂ} (f : Fun ℂ 1c) → f == empty

    _×c_   : Cat → Cat → Cat
    pair   : ∀{ℂ 𝔻 𝔼} → Fun 𝔼 ℂ → Fun 𝔼 𝔻 → Fun 𝔼 (ℂ ×c 𝔻)
    first  : ∀{ℂ 𝔻 𝔼} → Fun 𝔼 (ℂ ×c 𝔻) → Fun 𝔼 ℂ
    second : ∀{ℂ 𝔻 𝔼} → Fun 𝔼 (ℂ ×c 𝔻) → Fun 𝔼 𝔻
    pairβ1 : ∀{ℂ 𝔻 𝔼} (a : Fun 𝔼 ℂ) (b : Fun 𝔼 𝔻) → first (pair a b) == a
    pairβ2 : ∀{ℂ 𝔻 𝔼} (a : Fun 𝔼 ℂ) (b : Fun 𝔼 𝔻) → second (pair a b) == b
    pairη : ∀{ℂ 𝔻 𝔼} (p : Fun 𝔼 (ℂ ×c 𝔻)) → p == (pair (first p) (second p)) 

  {-# REWRITE pairβ1 #-}
  {-# REWRITE pairβ2 #-}


    
  
