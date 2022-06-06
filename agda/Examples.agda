{-# OPTIONS --rewriting #-}

open import Lib
open import STC
open import SubstitutionRewrites

module Examples where

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

{- work but slow

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

  fubini1 : ∀ {ℂ 𝔻 𝔼 𝔽} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel 𝔼 𝔽}
          → ((P ⊙ Q) ⊙ R) ≅i (P ⊙ (Q ⊙ R))
  fubini1 = ⊙-rec (⊙-rec (λe (λ▹ (λ▹ (λ▹ (pair⊙ v vt (pair⊙ v vt vt))))))) ,
            ⊙-rec (isIso.g exchange (⊙-rec (λe (λ▹ (λ▹ (λ◃ (pair⊙ v (pair⊙ v vt vt) vt))))))) ,
            ⊙-ext (⊙-ext id) ,
            ⊙-ext (exchange-ext (⊙-ext id))

  fubini2 : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
          → ((P ⊙ Q) ▹ R) ≅i (P ▹ (Q ▹ R))
  fubini2{P = P}{Q}{R} =
            λe (λ▹ (λ▹ (λ▹ (app▹ {ϕf = [ (P ⊙ Q) ▹ R ]} vt v (pair⊙ v vt vt))))) ,
            isIso.g exchange (⊙-rec (λe (λ▹ (λ▹ (λ◃ (app▹ (app▹ {ϕf = [ P ▹ (Q ▹ R)]} vt v vt) v vt)))))) ,
            induct-iso-lr exchange (⊙-ext id) ,
            ap λe (ap λ▹ (! (η▹ _) ∘ ap λ▹ (! (η▹ _)))) 

  fubini3 : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
          → (R ◃ (P ⊙ Q)) ≅i ((R ◃ P) ◃ Q)
  fubini3 {P = P}{Q}{R} =
          λe (λ▹ (λ◃ (λ◃ (app◃ {ϕa = [ P ] ,, [ Q ]} v (pair⊙ v vt vt) vt)))) ,
          (exchange-map (⊙-rec (λe (λ▹ (λ▹ (λ▹ (app◃ {ϕa = [ P ]} v vt (app◃ {ϕf = [ (R ◃ P) ◃ Q ]}{ϕa = [ Q ]} v vt vt)))))))) ,
          induct-iso-rl exchange (⊙-ext id) ,
          ap λe (ap λ▹ (! (η◃ _) ∘ ap λ◃ (! (η◃ _)))) 

    
  fubini4 : ∀ {ℂ 𝔻 𝔼} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel ℂ 𝔼}
          → (Q ▹ (R ◃ P)) ≅i ((Q ▹ R) ◃ P)
  fubini4 {P = P}{Q}{R} = λe (λ▹ (λ◃ (λ▹ ((app◃  {ϕf = ([ Q ▹ (R ◃ P) ] ,, [ Q ])} {ϕa = [ P ]} v vt (app▹ {ϕf = [ Q ▹ (R ◃ P) ]} {ϕa = [ Q ]} vt v vt)))))) ,
                          λe (λ▹ (λ▹ (λ◃ (app▹ (app◃  {ϕf = [ (Q ▹ R) ◃ P ]} {ϕa = [ P ] } v vt vt) v vt)))) ,
                          ap λe (ap λ▹ (! (η▹ _) ∘ ap λ▹ (! (η◃ _)))) ,
                          ap λe (ap λ▹ (! (η◃ _) ∘ ap λ◃ (! (η▹ _))))

  fubini5 : ∀ {ℂ 𝔻} {P Q : Rel ℂ 𝔻} → Iso (∀e {ℂ} (P ▹ Q)) (∀e {𝔻} (Q ◃ P))
  fubini5 = iso (\ f → λe (λ◃ (app▹ (appe f v) v vt)))
                (\ g → λe (λ▹ (app◃ v vt (appe g v))))
                (\x → ! (∀eη _) ∘ ap λe (! (η▹ _)))
                (\x → ! (∀eη _) ∘ ap λe (! (η◃ _)))  
-}
  
  ap-mor : ∀ {ℂ 𝔻} → (f : Fun ℂ 𝔻) → ∀e ((mor ℂ v v) ▹ mor 𝔻 (f · v) (f · v))
  ap-mor {ℂ}{𝔻} f = mor-rec _ (λe (ident f))

  -- diagramatic order
  compose1 : ∀ {ℂ} → ∀e (mor ℂ v v ▹ (mor ℂ v v ▹ mor ℂ v v ))
  compose1 = mor-rec _ (λe (λ▹ vt))

  compose2 : ∀ {ℂ} → ∀e (mor ℂ v v ▹ (mor ℂ v v ▹ mor ℂ v v ))
  compose2 = isIso.g exchange (mor-rec _ (λe (λ◃ vt)))

  compose1=2 : ∀ {ℂ} → compose1 {ℂ} == compose2 
  compose1=2 = mor-ext (mor-ext id)

  top-right : ∀ {ℂ} {𝔻} (F G : Fun ℂ 𝔻) (α : ∀e (mor 𝔻 F G)) → ∀e (mor ℂ v v ▹ mor 𝔻 F G)
  top-right F G α = λe (λ▹ (app▹ (app▹ (appe compose1 F) G (appe α v)) G (app▹ (appe (ap-mor G) v) v vt)  ))

  left-bottom : ∀ {ℂ} {𝔻} (F G : Fun ℂ 𝔻) (α : ∀e (mor 𝔻 F G)) → ∀e (mor ℂ v v ▹ mor 𝔻 F G)
  left-bottom F G α = λe (λ▹ (app▹ (app▹ (appe compose1 F) F ( app▹ (appe (ap-mor F) v) v vt )) G (appe α v )))

  naturality : ∀ {ℂ 𝔻} (F G : Fun ℂ 𝔻)
             → (α : ∀e (mor 𝔻 F G))
             → top-right F G α == left-bottom F G α
  naturality F G α = mor-ext {!!}

-- map in one dir but not the other?
-- Goal: (ϕ1 ,, ϕ2) ⊢ ((P [ f1 ∣ f2 ]) ⊙ (Q [ f2 ∣ f3 ]))
-- Have: (ϕ1 ,, ϕ2) ⊢ ((P [ f1 ∣ v ]) ⊙ (Q [ v ∣ f3 ]))
