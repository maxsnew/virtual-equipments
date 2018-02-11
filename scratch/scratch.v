Inductive dT (T : Set -> Set) (A : Set) : Set :=
| e : dT T A
| m : dT T A -> dT T A -> dT T A
| a : dT T (T A) -> dT T A
.

Axiom T : Set -> Set.
Axiom map : forall {A B : Set}, (A -> B) -> (T A -> T B).
Axiom eta : forall {B : Set}, B -> T B.
Axiom mu  : forall {B : Set}, T (T B) -> T B.
Definition tapp {A B : Set} (f : A -> T B) (tx : T A) : T B :=
  mu (map f tx).
  
Fixpoint plug {A} (dg : dT T A) (x : A) : T A :=
  match dg with
    | e => eta x
    | m dg' dd => tapp (plug dg') (plug dd x)
    | a dgg => mu (plug dgg (eta x))
  end.
