(* The representations [FSet A] and [FSetC A] are isomorphic for every A *)
Require Import HoTT HitTactics.
From representations Require Import cons_repr definition.
From fsets Require Import operations_cons_repr properties_cons_repr.

Section Iso.

  Context {A : Type}.
  Context `{Univalence}.

  Definition FSetC_to_FSet: FSetC A -> FSet A.
  Proof.
    hrecursion.
    - apply E.
    - intros a x.
      apply ({|a|} ∪ x).
    - intros. cbn.
      etransitivity. apply assoc.
      apply (ap (∪ x)).
      apply idem.
    - intros. cbn.
      etransitivity. apply assoc.
      etransitivity. refine (ap (∪ x) _ ).
      apply FSet.comm.
      symmetry.
      apply assoc.
  Defined.

  Definition FSet_to_FSetC: FSet A -> FSetC A.
  Proof.
    hrecursion.
    - apply ∅.
    - intro a. apply {|a|}.
    - intros X Y. apply (X ∪ Y).
    - apply append_assoc.
    - apply append_comm.
    - apply append_nl.
    - apply append_nr.
    - apply singleton_idem.
  Defined.

  Lemma append_union: forall (x y: FSetC A),
      FSetC_to_FSet (x ∪ y) = (FSetC_to_FSet x) ∪ (FSetC_to_FSet y).
  Proof.
    intros x.
    hrecursion x; try (intros; apply path_forall; intro; apply set_path2).
    - intros. symmetry. apply nl.
    - intros a x HR y. unfold union, fsetc_union in *. rewrite HR. apply assoc.
  Defined.

  Lemma repr_iso_id_l: forall (x: FSet A), FSetC_to_FSet (FSet_to_FSetC x) = x.
  Proof.
    hinduction; try (intros; apply set_path2).
    - reflexivity.
    - intro. apply nr.
    - intros x y p q. rewrite append_union, p, q. reflexivity.
  Defined.

  Lemma repr_iso_id_r: forall (x: FSetC A), FSet_to_FSetC (FSetC_to_FSet x) = x.
  Proof.
    hinduction; try (intros; apply set_path2).
    - reflexivity.
    - intros a x HR. rewrite HR. reflexivity.
  Defined.

  Global Instance: IsEquiv FSet_to_FSetC.
  Proof.
    apply isequiv_biinv.
    unfold BiInv. split.
    exists FSetC_to_FSet.
    unfold Sect. apply repr_iso_id_l.
    exists FSetC_to_FSet.
    unfold Sect. apply repr_iso_id_r.
  Defined.

  Global Instance: IsEquiv FSetC_to_FSet.
  Proof.
    change (IsEquiv (FSet_to_FSetC)^-1).
    apply isequiv_inverse.
  Defined.

  Theorem repr_iso: FSet A <~> FSetC A.
  Proof.
    simple refine (@BuildEquiv (FSet A) (FSetC A) FSet_to_FSetC _ ).
  Defined.

  Theorem fset_fsetc : FSet A = FSetC A.
  Proof.
    apply (equiv_path _ _)^-1.
    exact repr_iso.
  Defined.
End Iso.
