(* Operations on [FSet A] when [A] has decidable equality *)
Require Import HoTT HitTactics.
Require Export representations.definition fsets.operations.

Section decidable_A.
  Context {A : Type}.
  Context {A_deceq : DecidablePaths A}.
  Context `{Univalence}.

  Global Instance isIn_decidable : forall (a : A) (X : FSet A), Decidable (isIn a X).
  Proof.
    intros a.
    hinduction ; try (intros ; apply path_ishprop).
    - apply _.
    - intros. apply _.
    - intros. apply _. 
  Defined.

  Definition isIn_b (a : A) (X : FSet A) :=
    match dec (isIn a X) with
    | inl _ => true
    | inr _ => false
    end.
  
  Global Instance subset_decidable : forall (X Y : FSet A), Decidable (subset X Y).
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - intro ; apply _.
    - intros ; apply _. 
    - intros ; apply _.
  Defined.

  Definition subset_b (X Y : FSet A) :=
    match dec (subset X Y) with
    | inl _ => true
    | inr _ => false
    end.

  Definition intersection (X Y : FSet A) : FSet A := comprehension (fun a => isIn_b a Y) X. 

End decidable_A.