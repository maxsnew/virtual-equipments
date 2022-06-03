{-# OPTIONS --rewriting #-}

open import Lib
open import STC
open import SubstitutionRewrites

module Examples where

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

  fubini1 : ∀ {ℂ 𝔻 𝔼 𝔽} {P : Rel ℂ 𝔻} {Q : Rel 𝔻 𝔼} {R : Rel 𝔼 𝔽}
          → ((P ⊙ Q) ⊙ R) ≅i (P ⊙ (Q ⊙ R))
  fubini1 = ⊙-rec (⊙-rec (λe (λ▹ (λ▹ (λ▹ (pair⊙ v vt (pair⊙ v vt vt))))))) ,
            ⊙-rec (isIso.g exchange (⊙-rec (λe (λ▹ (λ▹ (λ◃ (pair⊙ v (pair⊙ v vt vt) vt))))))) ,
            ⊙-ext (⊙-ext {!!}) ,
            ⊙-ext {!!}


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
