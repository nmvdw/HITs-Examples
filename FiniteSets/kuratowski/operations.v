(** Operations on the [FSet A] for an arbitrary [A] *)
Require Import HoTT HitTactics.
Require Import kuratowski_sets monad_interface.

Section operations.
  (** Monad operations. *)
  Definition fset_fmap {A B : Type} : (A -> B) -> FSet A -> FSet B.
  Proof.
    intro f.
    hrecursion.
    - exact ∅.
    - apply (fun a => {|f a|}).
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
    - apply (idem o f).
  Defined.

  Global Instance fset_pure : hasPure FSet.
  Proof.
    split.
    apply (fun _ a => {|a|}).
  Defined.  

  Global Instance fset_bind : hasBind FSet.
  Proof.
    split.
    intros A.
    hrecursion.
    - exact ∅.
    - exact idmap.
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
    - apply union_idem.
  Defined.

  (** Set-theoretical operations. *)
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
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
    - intros.
      apply idem.
  Defined.

  Definition product {A B : Type} : FSet A -> FSet B -> FSet (A * B).
  Proof.
    intros X Y.
    hrecursion X.
    - apply ∅.
    - intro a.
      apply (single_product a Y).
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
    - intros ; apply union_idem.
  Defined.

  Local Ltac remove_transport
    := intros ; apply path_forall ; intro Z ; rewrite transport_arrow
       ; rewrite transport_const ; simpl.
  Local Ltac pointwise
    := repeat (f_ap) ; try (apply path_forall ; intro Z2) ;
      rewrite transport_arrow, transport_const, transport_sigma
      ; f_ap ; hott_simpl ; simple refine (path_sigma _ _ _ _ _)
      ; try (apply transport_const) ; try (apply path_ishprop).

  Context `{Univalence}.

  (** Separation axiom for finite sets. *)
  Definition separation (A B : Type) : forall (X : FSet A) (f : {a | a ∈ X} -> B), FSet B.
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

Section operations_decidable.
  Context {A : Type}.
  Context {A_deceq : DecidablePaths A}.
  Context `{Univalence}.

  Global Instance isIn_decidable (a : A) : forall (X : FSet A),
      Decidable (a ∈ X).
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - apply _.
    - intros b.
      destruct (dec (a = b)) as [p | np].
      * apply (inl (tr p)).
      * refine (inr(fun p => _)).
        strip_truncations.
        contradiction.
    - apply _. 
  Defined.

  Global Instance fset_member_bool : hasMembership_decidable (FSet A) A.
  Proof.
    intros a X.
    refine (if (dec a ∈ X) then true else false).
  Defined.

  Global Instance subset_decidable : forall (X Y : FSet A), Decidable (X ⊆ Y).
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - apply _.
    - apply _. 
    - unfold subset in *.
      apply _.
  Defined.

  Global Instance fset_subset_bool : hasSubset_decidable (FSet A).
  Proof.
    intros X Y.
    apply (if (dec (X ⊆ Y)) then true else false).
  Defined.

  Global Instance fset_intersection : hasIntersection (FSet A)
    := fun X Y => {|X & (fun a => a ∈_d Y)|}.
End operations_decidable.