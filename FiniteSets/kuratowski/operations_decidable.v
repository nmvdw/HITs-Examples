(* Operations on [FSet A] when [A] has decidable equality *)
Require Import HoTT HitTactics.
Require Export representations.definition fsets.operations.

Section decidable_A.
  Context {A : Type}.
  Context {A_deceq : DecidablePaths A}.
  Context `{Univalence}.
  
  Global Instance isIn_decidable : forall (a : A) (X : FSet A),
      Decidable (a ∈ X).
  Proof.
    intros a.
    hinduction ; try (intros ; apply path_ishprop).
    - apply _.
    - intros.
      unfold Decidable.
      destruct (dec (a = a0)) as [p | np].
      * apply (inl (tr p)).
      * right.
        intro p.
        strip_truncations.
        contradiction.
    - intros. apply _. 
  Defined.

  Global Instance fset_member_bool : hasMembership_decidable (FSet A) A.
  Proof.
    intros a X.
    destruct (dec (a ∈ X)).
    - apply true.
    - apply false.
  Defined.

  Global Instance subset_decidable : forall (X Y : FSet A), Decidable (X ⊆ Y).
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - intro ; apply _.
    - intros ; apply _. 
    - intros. unfold subset in *. apply _.
  Defined.

  Global Instance fset_subset_bool : hasSubset_decidable (FSet A).
  Proof.
    intros X Y.
    destruct (dec (X ⊆ Y)).
    - apply true.
    - apply false.
  Defined.

  Global Instance fset_intersection : hasIntersection (FSet A)
    := fun X Y => {|X & (fun a => a ∈_d Y)|}. 

End decidable_A.