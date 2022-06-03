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

  {- -- not used 
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

  subst-ident-vs : ∀ {ℂ} {R : Rel ℂ ℂ} 
                     → (s : vc ℂ ⊢ R )
                     → subst-tr s (vs v) == s
  subst-ident-vs s = subst-ident s

  subst-ident-P,,Q : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} →
                   ∀ {R} (t : ([ P ] ,, [ Q ]) ⊢ R)
                   → subst-tr t (,,s {ϕ1 = [ P ]} {ϕ2 = [ Q ]} v [ vt ]s [ vt ]s) == t
  subst-ident-P,,Q t = subst-ident t

{-
  subst-vt : ∀ {ℂ 𝔻} {ϕ1 : Ctx ℂ 𝔻} {R : Rel ℂ 𝔻}
               → (s : ϕ1 ⊢ R )
               → subst-tr {c = v} {d = v} vt [ s ]s == s
  subst-vt s = subst-vt-gen {f = v} {g = v} s
-}

  {-# REWRITE subst-ident #-}
  {-# REWRITE subst-vt-gen #-}
--  {-# REWRITE subst-vt #-}
  {-# REWRITE subst-ident-P,,Q #-}
  {-# REWRITE subst-ident-vs #-}

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

  -- why doesn't appe-subst cover this?
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
  -- {-# REWRITE app▹subst-unitr-ids #-}
  -- {-# REWRITE app▹subst-unitl-ids #-}
  
  -- can add more rules like this to approximate inversion further

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

  app▹subst-vs : {ℂ 𝔼 𝔻'' : Cat} {P : Rel ℂ 𝔼} {R : Rel ℂ 𝔼} 
                (s : vc ℂ ⊢ (P ▹ R))
                (a : Fun ℂ 𝔼)
                (t : vc ℂ ⊢ (P [ v ∣ a ]))
              → ∀ {h1 : Fun 𝔻'' ℂ}
              → _==_ 
                     (subst-tr (app▹ s a t) (vs h1))
                     ( (app▹ (s [ vs h1 ]tr) (a · h1) (t [ vs h1 ]tr)) )
  app▹subst-vs s a t {h1} = app▹subst s a t (vs h1) (vs h1) 

  app▹subst-vs-v : {ℂ 𝔻'' : Cat} {P : Rel ℂ ℂ} {R : Rel ℂ ℂ} 
                (s : vc ℂ ⊢ (P ▹ R))
                (t : vc ℂ ⊢ (P [ v ∣ v ]))
              → ∀ {h1 : Fun 𝔻'' ℂ}
              → _==_ 
                      (subst-tr (app▹ s v t) (vs h1))
                     ( (app▹ (s [ vs h1 ]tr) (h1) (t [ vs h1 ]tr)) )
  app▹subst-vs-v s t {h1} = app▹subst-vs s v t {h1}

  {-# REWRITE app▹subst-vs #-}
  {-# REWRITE app▹subst-vs-v #-}

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

  {-# REWRITE app▹subst-unitl-subst-v #-}
  {-# REWRITE app▹subst-unitl-subst #-}
  {-# REWRITE app▹subst-unitr-subst #-}
  {-# REWRITE app▹subst-unitr-subst-v #-}

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

  -- not sure why these are necessary

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

  -- associativity/unit inversions

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
  {-# REWRITE mor-recβ #-}
  
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

  postulate
    naturality? : ∀ {ℂ 𝔻 𝔼 : Cat} {P : Rel ℂ 𝔼} {Q : Rel 𝔼 𝔻} 
           → ∀ {ℂ' 𝔻' 𝔼' f1 f2 f3}
               {ϕ1 : Ctx ℂ' 𝔻'}  {ϕ2 : Ctx 𝔻' 𝔼'}  
               (x : ϕ1 ⊢ P [ f1 ∣ f2 ])
               (y : ϕ2 ⊢ Q [ f2 ∣ f3 ])
          → _==_{_}{ (ϕ1 ,, ϕ2) ⊢ (P ⊙ Q) [ f1 ∣ f3 ]}
                (app▹ (app▹ (appe (⊙i* {P = P [ f1 ∣ v ]} {Q = Q [ v ∣ f3 ]}) v) f2 x) v y)
                (app▹ (app▹ (appe (⊙i* {P = P} {Q = Q}) f1) f2 x) f3 y )

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
           ap (\ s → (app▹ (app▹ (appe s f1) f2 x) f3 y )) (⊙-recβ s) ∘ ap (app▹ (appe (isIso.g ⊙-rec-iso s) f1) f3)
           ( naturality? x y )

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
  {-# REWRITE ⊙-recβ #-}
  {-# REWRITE ⊙-recβ'-unitl #-}
  {-# REWRITE ⊙-recβ'-unitl-allv #-}
  {-# REWRITE ⊙-recβ'-unitr #-}
  {-# REWRITE ⊙-recβ'-unitr-allv #-}
  {-# REWRITE ⊙-recβ'-allv #-}

  ⊙-ext : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
          {f g : (P ⊙ Q) ⊸ R}
       → apply-to-pair f == apply-to-pair g
       → f == g
  ⊙-ext p = induct-iso-lr ⊙-rec-iso p

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

  ap-mor : ∀ {ℂ 𝔻} → (Fun ℂ 𝔻) → Set 
  ap-mor {ℂ}{𝔻} f = ∀e ((mor ℂ v v) ▹ mor 𝔻 (f · v) (f · v))

  exchange-map : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
           → (P ⊸ (Q ▹ R)) --  ∀ α. P(α,β) ▹(β) (Q(β,γ) ▹(γ) R(α,γ))
           → ((Q ⊸ (R ◃ P))) -- ∀ β. Q(β,γ) ▹(γ) (R(α,γ) ◃(α) P(α,β))
  exchange-map t = λe (λ▹ (λ◃ (app▹ (app▹ (appe t v) v vt) v vt)))

  exchange : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
           → isIso (P ⊸ (Q ▹ R)) ((Q ⊸ (R ◃ P))) exchange-map
  exchange {ℂ} {P = P}{Q}{R} = iso
                               (\ f → λe (λ▹ (λ▹ (app◃ v vt (app▹ (appe f v) v vt)))))
                               (\ f → ∀e-ext (! (η▹ _) ∘ ap λ▹ (! (η▹ _) ) ) )
                               \ f → ∀e-ext ((! (η▹ _) ∘ ap λ▹ ((! (η◃ _) )) ))

  exchange-ext : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
          {f g : (P ⊸ (Q ▹ R))}
       → exchange-map f == exchange-map g
       → f == g
  exchange-ext p = induct-iso-lr exchange p 

  yoneda-l : ∀ {ℂ 𝔻} (P : Rel ℂ 𝔻) → (mor 𝔻 v v ▹ P) ≅i P
  yoneda-l {ℂ} {𝔻} P = (λe (λ▹ ( app▹ vt v (ident v)))) ,
                       isIso.g exchange (mor-rec _ (λe (λ◃ vt)))  ,
                       exchange-ext (mor-ext id) ,
                       id

  yoneda-r : ∀ {ℂ 𝔻} (P : Rel ℂ 𝔻) → (P ◃ mor ℂ v v) ≅i P
  yoneda-r P = λe (λ▹ (app◃ v (ident v) vt )) ,
               exchange-map (mor-rec _ (λe (λ▹ vt))) ,
               induct-iso-rl exchange (mor-ext id) ,
               id

  coyoneda-l : ∀ {ℂ 𝔻} (P : Rel ℂ 𝔻) → (mor ℂ v v ⊙ P) ≅i P
  coyoneda-l P = ⊙-rec (mor-rec _ (λe (λ▹ vt))) ,
                 λe (λ▹ (pair⊙ v (ident v) vt)) ,
                 ⊙-ext (mor-ext id) ,
                 id

  coyoneda-r : ∀ {ℂ 𝔻} (P : Rel ℂ 𝔻) → (P ⊙ mor 𝔻 v v) ≅i P
  coyoneda-r P = ⊙-rec (isIso.g exchange (mor-rec _ (λe (λ◃ vt))) ) ,
                 λe (λ▹ (pair⊙ v vt (ident v))) ,
                 ⊙-ext (exchange-ext (mor-ext id)) ,
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


-- map in one dir but not the other?
-- Goal: (ϕ1 ,, ϕ2) ⊢ ((P [ f1 ∣ f2 ]) ⊙ (Q [ f2 ∣ f3 ]))
-- Have: (ϕ1 ,, ϕ2) ⊢ ((P [ f1 ∣ v ]) ⊙ (Q [ v ∣ f3 ]))
