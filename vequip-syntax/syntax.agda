module Syntax (Σ-sort : Set) where

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

    append : ∀ {C D E} -> Ctx C D -> Ctx D E -> Ctx C E
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
        cons : ∀ {C C' D D' E E'}
            -> (Φ : Ctx C D)
            -> (Φ' : Ctx D E)
            -> (A : Type C C')
            -> (B : Type D D')
            -> (B' : Type E E')
            -> (J : Judg C' D')
            -> (Ψ : Ctx D' E')
            -> Term Φ (restrict A B J)
            -> Subst Φ' B B' Ψ
            -> Subst (append Φ Φ') A B' (cons J Ψ)

      subst-term  : ∀ {C C' D D'}{A : Type C C'}{B : Type D D'}{Φ Ψ R}
                  -> Term Φ R
                  -> Subst Ψ A B Φ
                  -> Term Ψ (restrict A B R)
      comp-subst : ∀ {C C' C'' D D' D''}{A : Type C' C''}{A' : Type C C'}{B : Type D' D''}{B' : Type D D'}{Ψ Φ Θ}
                 -> Subst Ψ A B Φ
                 -> Subst Θ A' B' Ψ
                 -> Subst Θ (subst-type A A') (subst-type B B') Φ
      subst-term (var R) (end Φ A B .R t) = t
      subst-term (var R) (cons Φ Φ' A B B' .R .end t ())
      subst-term {Ψ = Ψ}(fun-app t ψ) φ = subst (λ S -> Term Ψ S) (restrict-assoc _ _ _ _ _) (fun-app t (comp-subst ψ φ)) -- {!fun-app t (comp-subst ψ φ)!}
      comp-subst φ ψ = {!!}
