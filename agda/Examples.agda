{-# OPTIONS --rewriting #-}

open import Lib
open import STC
open import SubstitutionRewrites

module Examples where

{- not true?  
  subst-external : ∀ {ℂ ℂ'} (P Q : Rel ℂ ℂ) (f : Fun ℂ' ℂ) → (∀e P → ∀e Q) → (∀e (P [ f ∣ f ]) → ∀e (Q [ f ∣ f ]))
  subst-external P Q f h p = coe {!!} (h (λe {!appe p v!}))
-}

  subst-internal : ∀ {ℂ 𝔻 ℂ' 𝔻'} (P Q : Rel ℂ 𝔻) (f : Fun ℂ' ℂ) (g : Fun 𝔻' 𝔻) → P ⊸ Q → P [ f ∣ g ] ⊸ Q [ f ∣ g ]
  subst-internal P Q f g h = (λe (λ▹ (app▹ (appe h f) g vt)))

  subst-≅i : ∀ {ℂ 𝔻 ℂ' 𝔻'} (P Q : Rel ℂ 𝔻) (f : Fun ℂ' ℂ) (g : Fun 𝔻' 𝔻) → P ≅i Q → P [ f ∣ g ] ≅i Q [ f ∣ g ]
  subst-≅i P Q f g ( l , r , lr , rl) = subst-internal P Q f g l ,
                                        subst-internal Q P f g r ,
                                        ap (subst-internal _ _ f g) lr ,
                                        ap (subst-internal _ _ f g) rl 

{- not true... like a deduction theorem 
  external-to-internal? : ∀ {ℂ} (P Q : Rel ℂ ℂ) → Iso (∀e P) (∀e Q) → P ≅i Q
  external-to-internal? P Q i = λe (λ▹ {!Iso.f i !})  ,
                                {!!} ,
                                {!!} ,
                                {!!}
-}

  internal-to-external : ∀ {ℂ} (P Q : Rel ℂ ℂ) → P ≅i Q → Iso (∀e P) (∀e Q) 
  internal-to-external P Q i = iso (\ t → λe (app▹ (appe (fst i) v) v (appe t v) ))
                                   (\ t → λe (app▹ (appe (fst (snd i)) v) v (appe t v) ))
                                   (\ x → ! (∀eη _) ∘ ap (\ (H : ∀e (P ▹ P)) →  λe (app▹ (appe H v) v (appe x v)) ) (fst (snd (snd i))))
                                   (\ x → ! (∀eη _) ∘ ap (\ (H ) →  λe (app▹ (appe H v) v (appe x v)) ) (snd (snd (snd i))))

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


  based-mor-rec-left : {ℂ 𝔻 : Cat} (Q : Rel ℂ 𝔻)
                → (f : Fun ℂ 𝔻)
                → ∀e (Q [ v ∣ f ])
                → ∀e {ℂ} (mor 𝔻 f v ▹ Q)
  based-mor-rec-left Q f b = λe (λ▹ ( app◃ v (appe b v) (app▹ (appe (mor-rec (Q ◃ Q) (λe (λ◃ vt))) f) v vt)))

  based-mor-rec-left-iso : {ℂ 𝔻 : Cat} (Q : Rel ℂ 𝔻)
                → (f : Fun ℂ 𝔻)
                → isIso (∀e (mor 𝔻 f v ▹ Q)) (∀e (Q [ v ∣ f ]))  (\ t → λe (app▹ (appe t v) f (ident f)))
  based-mor-rec-left-iso {𝔻 = 𝔻} Q f = iso (based-mor-rec-left Q f)
                                                  (λ x → ! (∀eη x) ∘
                                                     ap {M = λe (λ▹ (λ▹ (app◃ v (app▹ vt v (ident v)) (app▹ (appe (mor-rec (Q ◃ Q) (λe (λ◃ vt))) v) v vt))))}
                                                        {N = λe (λ▹ vt)}
                                                        -- tricky part is here!
                                                        (λ (h : ∀e (((mor _ v v ▹ Q)) ▹ (mor _ v v ▹ Q))) → λe ((app▹ (appe h v) f (appe x v))))
                                                        (exchange-ext (mor-ext id)  ))
                                                  (\ b → ! (∀eη _))

  based-mor-rec-right : {ℂ 𝔻 : Cat} (Q : Rel 𝔻 ℂ)
                → (f : Fun ℂ 𝔻)
                → ∀e (Q [ f ∣ v ])
                → ∀e (mor 𝔻 v f ▹ Q)
  based-mor-rec-right Q f b = λe (λ▹ (app▹ (app▹ (appe (mor-rec (Q ▹ Q) (λe (λ▹ vt))) v) f vt) v (appe b v)))

  based-mor-rec-right-iso : {ℂ 𝔻 : Cat} (Q : Rel 𝔻 ℂ)
                → (f : Fun ℂ 𝔻)
                → isIso (∀e {𝔻} (mor 𝔻 v f ▹ Q)) (∀e {ℂ} (Q [ f ∣ v ])) (\ t → λe (app▹  (appe t f) v (ident f) ) )
  based-mor-rec-right-iso Q f =
    iso (based-mor-rec-right Q f)
        (\ x → ! (∀eη x) ∘
                 ap λe (! (η▹ _)) ∘ 
                 (ap (\ z → λe (λ▹ (app◃ v vt (appe z v))))
                 (ap {M = λe (λ▹ (λ◃ (app▹ (app▹ (appe (mor-rec (Q ▹ Q) (λe (λ▹ vt))) v) v vt) v (app◃ v (ident v) vt)) ))}  
                     {N = λe (λ▹ vt)}
                    -- tricky part is here!
                    (λ (h : ∀e ((Q ◃ mor _ v v  ) ▹ (Q ◃ mor _ v v))) → λe (app▹ {ϕa = vc _}(appe h f) v (λ◃ (app▹ (appe x v) v vt))))
                    (induct-iso-rl exchange (mor-ext id))))
                 )
        (\ b → ! (∀eη _) ∘ {!!})

  yoneda-l : ∀ {ℂ 𝔻} (P : Rel ℂ 𝔻) → (mor 𝔻 v v ▹ P) ≅i P
  yoneda-l {ℂ} {𝔻} P = (λe (λ▹ ( app▹ vt v (ident v)))) ,
                       isIso.g exchange (mor-rec _ (λe (λ◃ vt)))  ,
                       exchange-ext (mor-ext id) ,
                       id

  based-mor-rec-left-iso-indirect : {ℂ 𝔻 : Cat} (Q : Rel ℂ 𝔻)
                → (f : Fun ℂ 𝔻)
                → Iso (∀e {ℂ} (mor 𝔻 f v ▹ Q)) (∀e {ℂ} (Q [ v ∣ f ])) 
  based-mor-rec-left-iso-indirect Q f = internal-to-external _ _ (subst-≅i _ Q v f (yoneda-l _))

  yoneda-r : ∀ {ℂ 𝔻} (P : Rel ℂ 𝔻) → (P ◃ mor ℂ v v) ≅i P
  yoneda-r P = λe (λ▹ (app◃ v (ident v) vt )) ,
               exchange-map (mor-rec _ (λe (λ▹ vt))) ,
               induct-iso-rl exchange (mor-ext id) ,
               id

  module Indirect where
    based-mor-rec-right-iso-indirect : {ℂ 𝔻 : Cat} (Q : Rel 𝔻 ℂ)
                  → (f : Fun ℂ 𝔻)
                  → Iso (∀e {ℂ} (Q ◃ mor 𝔻 v f)) (∀e {ℂ} (Q [ f ∣ v ])) 
    based-mor-rec-right-iso-indirect Q f =  internal-to-external (Q ◃ mor _ v f) (Q [ f ∣ v ]) (subst-≅i _ Q f v (yoneda-r Q))   
  
    based-mor-rec-right-iso' : {ℂ 𝔻 : Cat} (Q : Rel 𝔻 ℂ)
                  → (f : Fun ℂ 𝔻)
                  → isIso (∀e {𝔻} (mor 𝔻 v f ▹ Q)) (∀e {ℂ} (Q [ f ∣ v ])) (\ t → λe (app▹  (appe t f) v (ident f) ) )
    based-mor-rec-right-iso' Q f =
      iso (based-mor-rec-right Q f) -- could make a iso compose lemma and use fubini 5
          ( \x → (! (∀eη x) ∘ ap λe (! (η▹ _))  ) ∘ ap (\ H → λe (λ▹ (app◃ v vt (appe H v)))) ((Iso.gf (based-mor-rec-right-iso-indirect Q f) (λe (λ◃ (app▹ (appe x v) v vt))))) )
          ( \x →  (Iso.fg (based-mor-rec-right-iso-indirect Q f) x) ∘ {!!} )

{- work but slow


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

  module Naturality where
    
    top-right : ∀ {ℂ} {𝔻} (F G : Fun ℂ 𝔻) (α : ∀e (mor 𝔻 F G)) → ∀e (mor ℂ v v ▹ mor 𝔻 F G)
    top-right F G α = λe (λ▹ (app▹ (app▹ (appe compose1 F) G (appe α v)) G (app▹ (appe (ap-mor G) v) v vt)  ))
    
    left-bottom : ∀ {ℂ} {𝔻} (F G : Fun ℂ 𝔻) (α : ∀e (mor 𝔻 F G)) → ∀e (mor ℂ v v ▹ mor 𝔻 F G)
    left-bottom F G α = λe (λ▹ (app▹ (app▹ (appe compose1 F) F ( app▹ (appe (ap-mor F) v) v vt )) G (appe α v )))
    
    naturality : ∀ {ℂ 𝔻} (F G : Fun ℂ 𝔻)
               → (α : ∀e (mor 𝔻 F G))
               → top-right F G α == left-bottom F G α
    naturality {ℂ}{𝔻} F G α = mor-ext (ap (\ Q → λe (app▹ (app▹ (appe Q F) G (appe α v)) G (appe id0 G))) compose1=2    )

  BijectionAdjunction : {ℂ 𝔻 : Cat} (F : Fun 𝔻 ℂ) (G : Fun ℂ 𝔻)
                      → Set
  BijectionAdjunction {ℂ}{𝔻} F G = mor ℂ F v ≅i (mor 𝔻 v G)

  UnitCounitAdjunction : {ℂ 𝔻 : Cat} (F : Fun 𝔻 ℂ) (G : Fun ℂ 𝔻) → Set
  UnitCounitAdjunction F G =
    Σ \ (unit : ∀e (mor _ v (G · F))) → 
    Σ \ (counit : ∀e (mor _ (F · G) v)) → 
    _==_ {_}{∀e (mor _ F F)}
         (λe (app▹ (app▹ (appe compose1 F) (F · (G · F)) (app▹ (appe (ap-mor F) v) (G · F) (appe unit v))) F (appe counit F ))   )
         (λe (ident F))  ×
    _==_ {_}{∀e (mor _ G G)}
         (λe (app▹ (app▹ (appe compose1 G) (G · (F · G)) (appe unit G)) G (app▹ (appe (ap-mor G) (F · G)) v (appe counit v ) )))
         (λe (ident G))

{-  
  adj-naturality : ∀ {ℂ 𝔻} (F : Fun ℂ 𝔻) (G : Fun 𝔻 ℂ)
                 → (α : ∀e ((mor 𝔻 F v) ▹ (mor ℂ v G)))
                 → {!!}
  adj-naturality = {!!}
-}

  r-naturality-ident : {ℂ 𝔻 : Cat} (F : Fun 𝔻 ℂ) (G : Fun ℂ 𝔻)
                     → (r : mor 𝔻 v G ⊸ mor ℂ F v)
                     → _==_{_}{∀e (mor 𝔻 v G ▹ (mor _ F v))}
                         (λe (λ▹ (app▹ (app▹ (appe compose1 F) (F · G) (  (app▹ (appe (ap-mor F) v) G vt)  )) v
                                  (   (app▹ (appe r G) v (ident G)) ))))
                         (λe (λ▹ (app▹ (appe r v) v vt)))
  r-naturality-ident F G r = induct-iso-lr (based-mor-rec-right-iso (mor _ F v) G) {!!} 
                       

  to : {ℂ 𝔻 : Cat} (F : Fun 𝔻 ℂ) (G : Fun ℂ 𝔻)
    → BijectionAdjunction F G
    → UnitCounitAdjunction F G
  to F G (l , r , lr , rl) =  λe (app▹ (appe l v) F (ident F))  ,
                              λe (app▹ (appe r G) v (ident G)) ,
                              (ap (\ H → λe (app▹ (appe H v) F (ident F))) lr ∘
                               ap (\ H → λe (app▹ (appe H v) F (app▹ (appe l v) F (ident F)))) ( r-naturality-ident F G r ) ∘
                               {!!}) ,
                              ap (\ H → λe (app▹ (appe H G) v (ident G))) rl ∘ {!!}

{-
  from : {ℂ 𝔻 : Cat} (F : Fun 𝔻 ℂ) (G : Fun ℂ 𝔻)
    → UnitCounitAdjunction F G
    → BijectionAdjunction F G
  from F G (unit , counit , _) =
    λe (λ▹ (app▹ (app▹ (appe compose1 v) (G · F) (appe unit v)) G ( (app▹ (appe (ap-mor G) F) v vt) )  )) ,
    λe (λ▹ (app▹ (app▹ (appe compose1 F) (F · G) ( (app▹ (appe (ap-mor F) v) G vt) )) v (appe counit v)    )) ,
    {!!} ,
    {!!}
-}

  from : {ℂ 𝔻 : Cat} (F : Fun 𝔻 ℂ) (G : Fun ℂ 𝔻)
    → UnitCounitAdjunction F G
    → BijectionAdjunction F G
  from F G (unit , counit , triangle1 , triangle2) =
    based-mor-rec-left (mor _ v G) F unit  , 
    based-mor-rec-right (mor _ F v) G counit ,
    induct-iso-lr (based-mor-rec-left-iso (mor _ F v) F) (triangle1 ∘ {!!}) , 
    induct-iso-lr (based-mor-rec-right-iso (mor _ v G) G) (triangle2 ∘ {!!}) 


  mor-rec-◃-subst : ∀ {ℂ 𝔼 𝔼'} (P : Rel 𝔼 ℂ) (Q : Rel 𝔼 ℂ) (t : ∀e (Q ◃ P)) (f : Fun 𝔼' 𝔼)
            →  _==_{_}{∀e (mor ℂ v v ▹ (Q [ f ∣ v ] ◃ P [ f ∣ v ]))}
               (λe (λ▹ (λ◃ ( app◃ f vt (app▹ (appe (mor-rec (Q ◃ P) t) v) v vt)   ))) )
               (mor-rec (Q [ f ∣ v ] ◃ P [ f ∣ v ]) (λe (λ◃ (app◃ f vt (appe t v)))))
  mor-rec-◃-subst P Q t f = mor-ext id




  module Equipment where

    -- double category
    -- vertical arrows Fun
    -- horizontal arrows Rel, identity is mor 
    -- squares are [ R ] ⊢ S [ f ∣ g ]

    unit : ∀ {ℂ} → Rel ℂ ℂ
    unit = mor _ v v 

    Square : ∀ {ℂ 𝔻 ℂ' 𝔻'} (P : Rel ℂ 𝔻) (Q : Rel ℂ' 𝔻') (f : Fun ℂ ℂ') (g : Fun 𝔻 𝔻') →  Set
    Square P Q f g = ∀e (P ▹ Q [ f ∣ g ])

    horiz-ident : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻) → Square unit unit f f
    horiz-ident f = ap-mor f

    vert-ident : ∀ {ℂ 𝔻} (P : Rel ℂ 𝔻) → Square P P v v
    vert-ident P = λe (λ▹ vt)

    vertical-composition : ∀ {ℂ 𝔻 ℂ' 𝔻' ℂ'' 𝔻''} (P : Rel ℂ 𝔻) (Q : Rel ℂ' 𝔻') (R : Rel ℂ'' 𝔻'') (f : Fun ℂ ℂ') (g : Fun 𝔻 𝔻') (f' : Fun ℂ' ℂ'') (g' : Fun 𝔻' 𝔻'')
                         → Square P Q f g
                         → Square Q R f' g'
                         → Square P R (f' · f) (g' · g)
    vertical-composition P Q R f g f' g' s t = λe (λ▹ (app▹ (appe t f) g (app▹ (appe s v) v vt)))

    horizontal-composition : ∀ {ℂ 𝔻 𝔼 ℂ' 𝔻' 𝔼'} (P : Rel ℂ 𝔻) (P' : Rel 𝔻 𝔼)
                             (Q : Rel ℂ' 𝔻') (Q' : Rel 𝔻' 𝔼') (f : Fun ℂ ℂ') (g : Fun 𝔻 𝔻') 
                             (h : Fun 𝔼 𝔼') 
                           → Square P Q f g
                           → Square P' Q' g h
                           → Square (P ⊙ P') (Q ⊙ Q') f h
    horizontal-composition P P' Q Q' f g h s t = ⊙-rec (λe (λ▹ (λ▹ (pair⊙ g (app▹ (appe s v) v vt) ((app▹ (appe t v) v vt))))))

    companion : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻) → Rel ℂ 𝔻
    companion {ℂ}{𝔻} f = mor 𝔻 f v

    companion-square1 : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻) → Square (companion f) (unit) f v 
    companion-square1 f = vert-ident (companion f) -- works because of the type equalities! 

    companion-square2 : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻) → Square unit (companion f) v f
    companion-square2 f = horiz-ident f -- works because of the type equalities! 

    companion-equality1 : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻)
                        → _==_{_}{Square unit unit f f}
                          (vertical-composition unit (companion f) unit v f f v (companion-square2 f) (companion-square1 f) )
                          (horiz-ident f)
    companion-equality1 f = ! (∀eη _) ∘ ap λe (! (η▹ _))

    companion-equality2 : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻)
                        → _==_ (horizontal-composition unit (companion f) (companion f) unit v f v (companion-square2 f) (companion-square1 f))
                          (⊙-rec (mor-rec _ (λe (λ▹ (pair⊙ v vt (ident v)))))) -- inlined definitions of unitors
    companion-equality2 f = ⊙-ext (mor-ext (induct-iso-lr (based-mor-rec-left-iso _ f) {!!}))

    conjoint : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻) → Rel 𝔻 ℂ
    conjoint {ℂ}{𝔻} f = mor 𝔻 v f

    conjoint-square1 : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻) → Square unit (conjoint f) f v
    conjoint-square1 f = horiz-ident f

    conjoint-square2 : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻) → Square (conjoint f) (unit) v f
    conjoint-square2 f = vert-ident (conjoint f)

    conjoint-equality1 : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻)
                        → _==_{_}{Square unit unit f f}
                          (vertical-composition unit (conjoint f) unit f v v f (conjoint-square1 f) (conjoint-square2 f) )
                          (horiz-ident f)
    conjoint-equality1 f = ! (∀eη _) ∘ ap λe (! (η▹ _))

    conjoint-equality2 : ∀ {ℂ 𝔻} (f : Fun ℂ 𝔻)
                        → _==_ (horizontal-composition ((conjoint f)) unit unit (conjoint f) v f v (conjoint-square2 f) (conjoint-square1 f))
                               -- inlined definitions of unitors 
                               (⊙-rec (isIso.g exchange (mor-rec _ (λe (λ◃ (pair⊙ v (ident v) vt))))))
    conjoint-equality2 f = ⊙-ext (induct-iso-lr (based-mor-rec-right-iso _ f) (mor-ext {!!}))

    

-- map in one dir but not the other?
-- Goal: (ϕ1 ,, ϕ2) ⊢ ((P [ f1 ∣ f2 ]) ⊙ (Q [ f2 ∣ f3 ]))
-- Have: (ϕ1 ,, ϕ2) ⊢ ((P [ f1 ∣ v ]) ⊙ (Q [ v ∣ f3 ]))
