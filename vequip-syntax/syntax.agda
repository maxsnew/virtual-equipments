module Syntax (Σ-sort : Set) where

open import Data.Product
open import Relation.Binary.PropositionalEquality

-- A sort C,D,E identifies a set/cat/type theory
data Sort : Set where
  base : Σ-sort -> Sort

Type-type : Set₁
Type-type = Sort -> Sort -> Set

module VE1 (Σ-type : Type-type) where
  -- A : C -> D
  -- is a type of sort D parameterized by a type of sort C
  data Type : Type-type where
    x : ∀ (C : Sort) -> Type C C
    base : ∀ {C D E : Sort} (F : Σ-type C D) -> Type E C -> Type E D

  subst-type : ∀ {C D E : Sort} -> Type C D -> Type E C -> Type E D
  subst-type (x C) a = a
  subst-type (base F f) a = base F (subst-type f a)
  
  -- TODO: assoc, unit
  subst-type-assoc : ∀ {C C' C'' C'''}(A : Type C'' C''')(A' : Type C' C'')(A'' : Type C C')
                   -> subst-type (subst-type A A') A'' ≡ subst-type A (subst-type A' A'')
  subst-type-assoc (x C) A' A'' = refl
  subst-type-assoc (base F A) A' A'' = cong (base F) (subst-type-assoc A A' A'')

  Judg-type : Set₁
  Judg-type = Type-type

  module VE2 (Σ-judg : Judg-type) where
    -- A judgment |- : Judg C D is a "set" of terms
    -- - contravariantly indexed by a type of sort C
    -- - covariantly indexed by a type of sort D
    
    data Judg : Judg-type where
      base : ∀ {C C' D D' : Sort} (A : Type C C') (B : Type D D') (R : Σ-judg C' D') -> Judg C D

    restrict : ∀ {C C' D D' : Sort} (A : Type C C') (B : Type D D') (R : Judg C' D') -> Judg C D
    restrict A B (base A' B' R) = base (subst-type A' A) (subst-type B' B) R

    -- TODO: assoc, unit of restrict, maybe one-sided restriction too
    restrict-assoc : ∀ {C C' C'' D D' D''}(A : Type C' C'') (A' : Type C C') (B : Type D' D'') (B' : Type D D') R
                   -> restrict (subst-type A A') (subst-type B B') R ≡ restrict A' B' (restrict A B R)
    restrict-assoc A A' B B' (base A'' B'' R) = cong₂ (λ AAA BBB → base AAA BBB R) (sym (subst-type-assoc A'' A A')) (sym (subst-type-assoc B'' B B'))

    -- | A "composable string" of judgments
    data Ctx : Judg-type where
      end  : ∀ {C} -> Ctx C C
      cons : ∀ {C D E} -> Judg C D -> Ctx D E -> Ctx C E

    append : ∀ {C midSort E} -> Ctx C midSort -> Ctx midSort E -> Ctx C E
    append end Ψ = Ψ
    append (cons R Φ) Ψ = cons R (append Φ Ψ)

    Term-type : Set₁
    Term-type = ∀ {C D} -> Ctx C D -> Judg C D -> Set

    module VE3 (Σ-term : Term-type) where

      data Term : Term-type
      data Subst : ∀ {C C' D D'} -> Ctx C D -> Type C C' -> Type D D' -> Ctx C' D' -> Set
      data Term where
        var : ∀ {C D} (R : Judg C D) -> Term (cons R end) R
        fun-app : ∀ {C C' D D'}{A : Type C C'}{B : Type D D'}{Φ Ψ R}
                -> (Σ-term Φ R)
                -> Subst Ψ A B Φ
                -> Term Ψ (restrict A B R)
      data Subst where
        end : ∀ {C C' D D'}
            -> (Φ : Ctx C D)
            -> (A : Type C C')
            -> (B : Type D D')
            -> (J : Judg C' D')
            -> Term Φ (restrict A B J)
            -> Subst Φ A B (cons J end)
        cons : ∀ {C C' D D' E' F F'}
            -> (Φ : Ctx C D)
            -> (Φ' : Ctx D F)
            -> (A : Type C C')
            -> (B : Type D D')
            -> (B' : Type F F')
            -> (J : Judg C' D')
            -> (K : Judg D' E')
            -> (Ψ : Ctx E' F')
            -> Term Φ (restrict A B J)
            -> Subst Φ' B B' (cons K Ψ)
            -> Subst (append Φ Φ') A B' (cons J (cons K Ψ))

      subst-term  : ∀ {C C' D D'}{A : Type C C'}{B : Type D D'}{Φ Ψ R}
                  -> Term Φ R
                  -> Subst Ψ A B Φ
                  -> Term Ψ (restrict A B R)
      comp-subst : ∀ {C C' C'' D D' D''}{A : Type C' C''}{A' : Type C C'}{B : Type D' D''}{B' : Type D D'}{Ψ Φ Θ}
                 -> Subst Ψ A B Φ
                 -> Subst Θ A' B' Ψ
                 -> Subst Θ (subst-type A A') (subst-type B B') Φ
      subst-term (var R) (end Φ A B .R t) = t
      subst-term {Ψ = Ψ}(fun-app t ψ) φ = subst (λ S -> Term Ψ S) (restrict-assoc _ _ _ _ _) (fun-app t (comp-subst ψ φ)) -- {!fun-app t (comp-subst ψ φ)!}
      comp-subst {Θ = Θ} (end Φ A B J t) φ =
        end _ _ _ _ (subst (λ J₁ → Term Θ J₁) (sym (restrict-assoc A _ B _ J)) (subst-term t φ))
      -- | want a (Θ -> (J, K, Ψ)) and have φ : (Θ -> (Φ, Φ')) and a t : (Φ -> J) and a ψ : (Φ' -> (K, Ψ))
      comp-subst (cons end Φ' A B B' J K Ψ t ψ) φ = {!subst (λ Θ -> Subst Θ (subst-type A A') (subst-type B' )) !}
      comp-subst (cons (cons L end) Φ' A B B' J K Ψ t ψ) φ = {!!}
      comp-subst (cons (cons L (cons x₁ Φ)) Φ' A B B' J K Ψ t ψ) φ = {!!}

      -- record Split-Subst {C C' D D' E'}(F : Type C C')(H : Type D D')(Θ : Ctx C D)(Φ1 : Ctx C' E')(Φ2 : Ctx E' D') : Set where
      --   field
      --     E  : Sort
      --     G  : Type E E'
      --     Θ1 : Ctx C E
      --     Θ2 : Ctx E D
      --     φ  : Subst Θ1 F G Φ1
      --     φ' : Subst Θ2 G H Φ2

      -- -- | PLAN: induction on Φ1
      -- split-subst : ∀ {C C' D D' E'}{F : Type C C'}{H : Type D D'}{Ψ}{Φ1 Φ2}
      --             -> Subst Ψ F H (append {midSort = E'} Φ1 Φ2)
      --             -> Split-Subst F H Ψ Φ1 Φ2
      -- split-subst {Ψ = .Φ} {end} {.(cons J end)} (end Φ A B J x₁) = {!!} -- record { E = ? ; G = ? ; Θ1 = end ; Θ2 = Ψ ; φ = ? ; φ' = ? }
      -- split-subst {Ψ = .(append Φ Φ')} {end} {.(cons J Ψ)} (cons Φ Φ' A B B' J Ψ x₁ φφ) = {!!} -- record { E = ? ; G = ? ; Θ1 = end ; Θ2 = Ψ ; φ = ? ; φ' = ? }
      -- split-subst {Φ1 = cons x₁ Φ1} φφ = {!!}

