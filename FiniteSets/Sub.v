Require Import HoTT.
Require Import disjunction lattice notation.

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

  Theorem decidable_A_isIn : forall a b : A, Decidable (Trunc (-1) (b = a)).
  Proof.
    intros.
    unfold Decidable, closedSingleton in *.
    pose (HIn {|a|} (HS a) b).
    destruct s.
    - unfold singleton in t.
      left.
      apply t.
    - right.
      intro p.
      unfold singleton in n.
      strip_truncations.
      contradiction (n (tr p)).
  Defined.

End isIn.

Section intersect.
  Variable A : Type.
  Variable C : (Sub A) -> hProp.
  Context `{Univalence}.

  Global Instance hprop_lem : forall (T : Type) (Ttrunc : IsHProp T), IsHProp (T + ~T).
  Proof.
    intros.
    apply (equiv_hprop_allpath _)^-1.
    intros [x | nx] [y | ny] ; try f_ap ; try (apply Ttrunc) ; try contradiction.
    - apply equiv_hprop_allpath. apply _.
  Defined.

  Context
    {HI : closedIntersection C} {HE : closedEmpty C}
    {HS : closedSingleton C} {HDE : hasDecidableEmpty C}.

  Theorem decidable_A_intersect : forall a b : A, Decidable (Trunc (-1) (b = a)).
  Proof.
    intros.
    unfold Decidable, closedEmpty, closedIntersection, closedSingleton, hasDecidableEmpty in *.
    pose (HI {|a|} {|b|} (HS a) (HS b)) as IntAB.
    pose (HDE ({|a|} ∪ {|b|}) IntAB) as IntE.
    refine (@Trunc_rec _ _ _  _ _ IntE) ; intros [p | p] ; unfold min_fun, singleton in p.
    - right.
      intro q.
      strip_truncations.
      rewrite q in p.
      enough (a ∈ ∅) as X.
      { apply X. }
      rewrite <- p.
      cbn.
      split ; apply (tr idpath).
    - strip_truncations.
      destruct p as [a0 [t1 t2]].
      strip_truncations.
      apply (inl (tr (t2^ @ t1))).
  Defined.
End intersect.
