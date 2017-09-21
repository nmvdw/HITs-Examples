(** The representations [FSet A] and [FSetC A] are isomorphic for every A *)
Require Import HoTT HitTactics.
Require Import list_representation list_representation.operations
        list_representation.properties.
Require Import kuratowski.kuratowski_sets.

Section Iso.
  Context {A : Type}.

  Definition FSetC_to_FSet: FSetC A -> FSet A.
  Proof.
    hrecursion.
    - apply ∅.
    - intros a x.
      apply ({|a|} ∪ x).
    - intros a X.
      apply (assoc _ _ _ @ ap (∪ X) (idem _)).
    - intros a X Y.
      apply (assoc _ _ _ @ ap (∪ Y) (comm _ _) @ (assoc _ _ _)^).
  Defined.

  Definition FSet_to_FSetC: FSet A -> FSetC A.
  Proof.
    hrecursion.
    - apply ∅.
    - apply (fun a => {|a|}).
    - apply (∪).
    - apply append_assoc.
    - apply append_comm.
    - apply append_nl.
    - apply append_nr.
    - apply singleton_idem.
  Defined.

  Lemma append_union: forall (x y: FSetC A),
      FSetC_to_FSet (x ∪ y) = (FSetC_to_FSet x) ∪ (FSetC_to_FSet y).
  Proof.
    intros x y.
    hrecursion x ; try (intros ; apply path_ishprop).
    - intros.
      apply (nl _)^.
    - intros a x HR.
      refine (ap ({|a|} ∪) HR @ assoc _ _ _).
  Defined.

  Lemma repr_iso_id_l: forall (x: FSet A), FSetC_to_FSet (FSet_to_FSetC x) = x.
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - reflexivity.
    - intro.
      apply nr.
    - intros x y p q.
      refine (append_union _ _ @ _).
      refine (ap (∪ _) p @ _).
      apply (ap (_ ∪) q).
  Defined.

  Lemma repr_iso_id_r: forall (x: FSetC A), FSet_to_FSetC (FSetC_to_FSet x) = x.
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - reflexivity.
    - intros a x HR.
      refine (ap ({|a|} ∪) HR).
  Defined.

  Global Instance: IsEquiv FSet_to_FSetC.
  Proof.
    apply isequiv_biinv.
    split.
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

  Theorem fset_fsetc `{Univalence} : FSet A = FSetC A.
  Proof.
    apply (equiv_path _ _)^-1.
    exact repr_iso.
  Defined.

  Definition dupl' (a : A) (X : FSet A) : {|a|} ∪ {|a|} ∪ X = {|a|} ∪ X
    := assoc _ _ _ @ ap (∪ X) (idem a).

  Definition comm' (a b : A) (X : FSet A) : {|a|} ∪ {|b|} ∪ X = {|b|} ∪ {|a|} ∪ X
    := assoc _ _ _ @ ap (∪ X) (comm _ _) @ (assoc _ _ _)^.
  
  Theorem FSet_cons_ind (P : FSet A -> Type)
    (Pset : forall (X : FSet A), IsHSet (P X))
    (Pempt : P ∅)
    (Pcons : forall (a : A) (X : FSet A), P X -> P ({|a|} ∪ X))
    (Pdupl : forall (a : A) (X : FSet A) (px : P X),
       transport P (dupl' a X) (Pcons a _ (Pcons a X px)) = Pcons a X px)
    (Pcomm : forall (a b : A) (X : FSet A) (px : P X),
        transport P (comm' a b X) (Pcons a _ (Pcons b X px)) = Pcons b _ (Pcons a X px))
    (X : FSet A)
    : P X.
  Proof.
    refine (transport P (repr_iso_id_l X) _).
    simple refine (FSetC_ind A (fun Z => P (FSetC_to_FSet Z)) _ _ _ _ _ (FSet_to_FSetC X))
    ; simpl.
    - apply Pempt.
    - intros a Y HY.
      apply (Pcons a _ HY).
    - intros a Y PY.
      refine (_ @ (Pdupl _ _ _)).
      refine (transport_compose _ FSetC_to_FSet (dupl a Y) _ @ _).
      refine (ap (fun z => transport P z _) _).
      apply path_ishprop.
    - intros a b Y PY.
      refine (transport_compose _ FSetC_to_FSet (comm_s a b Y) _ @ _ @ (Pcomm _ _ _ _)).
      refine (ap (fun z => transport P z _) _).
      apply path_ishprop.
  Defined.

  (*
  Theorem FSet_cons_ind_beta_empty (P : FSet A -> Type)
    (Pset : forall (X : FSet A), IsHSet (P X))
    (Pempt : P ∅)
    (Pcons : forall (a : A) (X : FSet A), P X -> P ({|a|} ∪ X))
    (Pdupl : forall (a : A) (X : FSet A) (px : P X),
       transport P (dupl' a X) (Pcons a _ (Pcons a X px)) = Pcons a X px)
    (Pcomm : forall (a b : A) (X : FSet A) (px : P X),
       transport P (comm' a b X) (Pcons a _ (Pcons b X px)) = Pcons b _ (Pcons a X px)) :
    FSet_cons_ind P Pset Pempt Pcons Pdupl Pcomm ∅ = Pempt.
  Proof.
      by compute.
  Defined.

  
  Theorem FSet_cons_ind_beta_cons (P : FSet A -> Type)
          (Pset : forall (X : FSet A), IsHSet (P X))
          (Pempt : P ∅)
          (Pcons : forall (a : A) (X : FSet A), P X -> P ({|a|} ∪ X))
          (Pdupl : forall (a : A) (X : FSet A) (px : P X),
              transport P (dupl' a X) (Pcons a _ (Pcons a X px)) = Pcons a X px)
          (Pcomm : forall (a b : A) (X : FSet A) (px : P X),
              transport P (comm' a b X) (Pcons a _ (Pcons b X px)) = Pcons b _ (Pcons a X px)) :
    forall a X, FSet_cons_ind P Pset Pempt Pcons Pdupl Pcomm ({|a|} ∪ X)
                = Pcons a X (FSet_cons_ind P Pset Pempt Pcons Pdupl Pcomm X).
  Proof.
    intros.
    unfold FSet_cons_ind.
    simpl.
    rewrite ?transport_pp.
    hinduction X ; try(intros ; apply path_ishprop) ; simpl.
    - admit.
    - intro b.
      unfold FSet_cons_ind.
      simpl.
      admit.
    - intros.
      unfold FSet_cons_ind.
      simpl.
      rewrite X.
    *)  
End Iso.
