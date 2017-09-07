Require Import HoTT.
Require Import set_names lattice_interface lattice_examples prelude.

Section subobjects.
  Variable A : Type.

  Definition Sub := A -> hProp.

  Global Instance sub_empty : hasEmpty Sub := fun _ => False_hp.
  Global Instance sub_union : hasUnion Sub := max_fun.
  Global Instance sub_intersection : hasIntersection Sub := min_fun.
  Global Instance sub_singleton : hasSingleton Sub A
    := fun a b => BuildhProp (Trunc (-1) (b = a)).
  Global Instance sub_membership : hasMembership Sub A := fun a X => X a.
  Global Instance sub_comprehension : hasComprehension Sub A
    := fun ϕ X a => BuildhProp (X a * (ϕ a = true)).
  Global Instance sub_subset `{Univalence} : hasSubset Sub
    := fun X Y => BuildhProp (forall a, X a -> Y a).

End subobjects.

Section sub_classes.
  Context {A : Type}.
  Variable C : (A -> hProp) -> hProp.
  Context `{Univalence}.

  Instance subobject_lattice : Lattice (Sub A).
  Proof.
    apply _.
  Defined.  

  Definition closedUnion := forall X Y, C X -> C Y -> C (X ∪ Y).
  Definition closedIntersection := forall X Y, C X -> C Y -> C (X ∩ Y).
  Definition closedEmpty := C ∅.
  Definition closedSingleton := forall a, C {|a|}.
  Definition hasDecidableEmpty := forall X, C X -> hor (X = ∅) (hexists (fun a => a ∈ X)).
End sub_classes.

Section isIn.
  Variable A : Type.
  Variable C : (A -> hProp) -> hProp.

  Context `{Univalence}.
  Context {HS : closedSingleton C} {HIn : forall X, C X -> forall a, Decidable (X a)}.

  Theorem decidable_A_isIn (a b : A) : Decidable (Trunc (-1) (b = a)).
  Proof.
    destruct (HIn {|a|} (HS a) b).
    - apply (inl t).
    - refine (inr(fun p => _)).
      strip_truncations.
      contradiction (n (tr p)).
  Defined.

End isIn.

Section intersect.
  Variable A : Type.
  Variable C : (Sub A) -> hProp.
  Context `{Univalence}
    {HI : closedIntersection C} {HE : closedEmpty C}
    {HS : closedSingleton C} {HDE : hasDecidableEmpty C}.

  Theorem decidable_A_intersect (a b : A) : Decidable (Trunc (-1) (b = a)).
  Proof.
    unfold Decidable.
    pose (HI {|a|} {|b|} (HS a) (HS b)) as IntAB.
    pose (HDE ({|a|} ∪ {|b|}) IntAB) as IntE.
    refine (Trunc_rec _ IntE) ; intros [p | p].
    - refine (inr(fun q => _)).
      strip_truncations.
      refine (transport (fun Z => a ∈ Z) p (tr idpath, tr q^)).
    - strip_truncations.
      destruct p as [? [t1 t2]].
      strip_truncations.
      apply (inl (tr (t2^ @ t1))).
  Defined.
End intersect.