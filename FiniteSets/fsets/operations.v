(* Operations on the [FSet A] for an arbitrary [A] *)
Require Import HoTT HitTactics.
Require Import representations.definition disjunction lattice.

Section operations.
  Context `{Univalence}.

  Global Instance fset_member : forall A, hasMembership (FSet A) A.
  Proof.
    intros A a.
    hrecursion.
    - exists Empty.
      exact _.
    - intro a'.
      exists (Trunc (-1) (a = a')).
      exact _.
    - apply lor.
    - intros ; symmetry ; apply lor_assoc.
    - apply lor_commutative.
    - apply lor_nl.
    - apply lor_nr.
    - intros ; apply lor_idem.
  Defined.

  Global Instance fset_comprehension : forall A, hasComprehension (FSet A) A.
  Proof.
    intros A P.
    hrecursion.
    - apply ∅.
    - intro a.
      refine (if (P a) then {|a|} else ∅).
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
    - intros; simpl.
      destruct (P x).
      + apply idem.
      + apply nl.
  Defined.

  Definition isEmpty (A : Type) :
    FSet A -> Bool.
  Proof.
    simple refine (FSet_rec _ _ _ true (fun _ => false) andb _ _ _ _ _)
    ; try eauto with bool_lattice_hints typeclass_instances.
  Defined.

  Definition single_product {A B : Type} (a : A) : FSet B -> FSet (A * B).
  Proof.
    hrecursion.
    - apply ∅.
    - intro b.
      apply {|(a, b)|}.
    - apply (∪).
    - intros X Y Z ; apply assoc.
    - intros X Y ; apply comm.
    - intros ; apply nl.
    - intros ; apply nr.
    - intros ; apply idem.
  Defined.

  Definition product {A B : Type} : FSet A -> FSet B -> FSet (A * B).
  Proof.
    intros X Y.
    hrecursion X.
    - apply ∅.
    - intro a.
      apply (single_product a Y).
    - apply (∪).
    - intros ; apply assoc.
    - intros ; apply comm.
    - intros ; apply nl.
    - intros ; apply nr.
    - intros ; apply union_idem.
  Defined.

  Global Instance fset_subset : forall A, hasSubset (FSet A).
  Proof.
    intros A X Y.
    hrecursion X.
    - exists Unit.
      exact _.
    - intros a.
      apply (a ∈ Y).
    - intros X1 X2.
      exists (prod X1 X2).
      exact _.
    - intros.
      apply path_trunctype ; apply equiv_prod_assoc.
    - intros.
      apply path_trunctype ; apply equiv_prod_symm.
    - intros.
      apply path_trunctype ; apply prod_unit_l.
    - intros.
      apply path_trunctype ; apply prod_unit_r.
    - intros a'.
      apply path_iff_hprop ; cbn.
      * intros [p1 p2]. apply p1.
      * intros p.
        split ; apply p.
  Defined.

  Local Ltac remove_transport
    := intros ; apply path_forall ; intro Z ; rewrite transport_arrow
       ; rewrite transport_const ; simpl.
  Local Ltac pointwise
    := repeat (f_ap) ; try (apply path_forall ; intro Z2) ;
      rewrite transport_arrow, transport_const, transport_sigma
      ; f_ap ; hott_simpl ; simple refine (path_sigma _ _ _ _ _)
      ; try (apply transport_const) ; try (apply path_ishprop).

  Lemma separation (A B : Type) : forall (X : FSet A) (f : {a | a ∈ X} -> B), FSet B.
  Proof.
    hinduction.
    - intros f.
      apply ∅.
    - intros a f.
      apply {|f (a; tr idpath)|}.
    - intros X1 X2 HX1 HX2 f.
      pose (fX1 := fun Z : {a : A & a ∈ X1} => f (pr1 Z;tr (inl (pr2 Z)))).
      pose (fX2 := fun Z : {a : A & a ∈ X2} => f (pr1 Z;tr (inr (pr2 Z)))).
      specialize (HX1 fX1).
      specialize (HX2 fX2).
      apply (HX1 ∪ HX2).
    - remove_transport.
      rewrite assoc.
      pointwise.
    - remove_transport.
      rewrite comm.
      pointwise.
    - remove_transport.
      rewrite nl.
      pointwise.
    - remove_transport.
      rewrite nr.
      pointwise.
    - remove_transport.
      rewrite <- (idem (Z (x; tr 1%path))).
      pointwise.
  Defined.

End operations.
