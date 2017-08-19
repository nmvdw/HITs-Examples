(* The representations [FSet A] and [FSetC A] are isomorphic for every A *)
Require Import HoTT HitTactics.
From representations Require Import cons_repr definition.
From fsets Require Import operations_cons_repr properties_cons_repr.

Section Iso.

  Context {A : Type}.
  Context `{Univalence}.

  Definition dupl' (a : A) (X : FSet A) :
    {|a|} ∪ {|a|} ∪ X = {|a|} ∪ X := assoc _ _ _ @ ap (∪ X) (idem _).
  Definition comm' (a b : A) (X : FSet A) :
    {|a|} ∪ {|b|} ∪ X = {|b|} ∪ {|a|} ∪ X :=
    assoc _ _ _ @ ap (∪ X) (comm _ _) @ (assoc _ _ _)^.

  Definition FSetC_to_FSet: FSetC A -> FSet A.
  Proof.
    hrecursion.
    - apply E.
    - intros a x.
      apply ({|a|} ∪ x).
    - intros. cbn.
      apply dupl'.
    - intros. cbn.
      apply comm'.
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
    - intros a x HR y. unfold union, fsetc_union in *.
      refine (_ @ assoc _ _ _).
      apply (ap ({|a|} ∪) (HR _)).
  Defined.

  Lemma repr_iso_id_l: forall (x: FSet A), FSetC_to_FSet (FSet_to_FSetC x) = x.
  Proof.
    hinduction; try (intros; apply set_path2).
    - reflexivity.
    - intro. apply nr.
    - intros x y p q.
      refine (append_union _ _ @ _).
      refine (ap (∪ _) p @ _).
      apply (ap (_ ∪) q).
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

  Theorem FSet_cons_ind (P : FSet A -> Type)
    (Pset : forall (X : FSet A), IsHSet (P X))
    (Pempt : P ∅)
    (Pcons : forall (a : A) (X : FSet A), P X -> P ({|a|} ∪ X))
    (Pdupl : forall (a : A) (X : FSet A) (px : P X),
       transport P (dupl' a X) (Pcons a _ (Pcons a X px)) = Pcons a X px)
    (Pcomm : forall (a b : A) (X : FSet A) (px : P X),
       transport P (comm' a b X) (Pcons a _ (Pcons b X px)) = Pcons b _ (Pcons a X px)) :
    forall X, P X.
  Proof.
    intros X.
    refine (transport P (repr_iso_id_l X) _).
    simple refine (FSetC_ind A (fun Z => P (FSetC_to_FSet Z)) _ _ _ _ _ (FSet_to_FSetC X)); simpl.
    - apply Pempt.
    - intros a Y HY. by apply Pcons.
    - intros a Y PY. cbn.
      refine (_ @ (Pdupl _ _ _)).
      etransitivity.
      { apply (transport_compose _ FSetC_to_FSet (dupl a Y)). }
      refine (ap (fun z => transport P z _) _).
      apply FSetC_rec_beta_dupl.
    - intros a b Y PY. cbn.
      refine (_ @ (Pcomm _ _ _ _)).
      etransitivity.
      { apply (transport_compose _ FSetC_to_FSet (FSetC.comm a b Y)). }
      refine (ap (fun z => transport P z _) _).
      apply FSetC_rec_beta_comm.
  Defined.

  Theorem FSet_cons_ind_beta_empty (P : FSet A -> Type)
    (Pset : forall (X : FSet A), IsHSet (P X))
    (Pempt : P ∅)
    (Pcons : forall (a : A) (X : FSet A), P X -> P ({|a|} ∪ X))
    (Pdupl : forall (a : A) (X : FSet A) (px : P X),
       transport P (dupl' a X) (Pcons a _ (Pcons a X px)) = Pcons a X px)
    (Pcomm : forall (a b : A) (X : FSet A) (px : P X),
       transport P (comm' a b X) (Pcons a _ (Pcons b X px)) = Pcons b _ (Pcons a X px)) :
    FSet_cons_ind P Pset Pempt Pcons Pdupl Pcomm ∅ = Pempt.
  Proof. by compute. Defined.

  (* TODO *)
  (* Theorem FSet_cons_ind_beta_cons (P : FSet A -> Type)  *)
  (*   (Pset : forall (X : FSet A), IsHSet (P X)) *)
  (*   (Pempt : P ∅) *)
  (*   (Pcons : forall (a : A) (X : FSet A), P X -> P ({|a|} ∪ X)) *)
  (*   (Pdupl : forall (a : A) (X : FSet A) (px : P X), *)
  (*      transport P (dupl' a X) (Pcons a _ (Pcons a X px)) = Pcons a X px) *)
  (*   (Pcomm : forall (a b : A) (X : FSet A) (px : P X), *)
  (*      transport P (comm' a b X) (Pcons a _ (Pcons b X px)) = Pcons b _ (Pcons a X px)) : *)
  (*   forall a X, FSet_cons_ind P Pset Pempt Pcons Pdupl Pcomm ({|a|} ∪ X) = Pcons a X (FSet_cons_ind P Pset Pempt Pcons Pdupl Pcomm X). *)
  (* Proof.     *)

  (* Theorem FSet_cons_ind_beta_dupl (P : FSet A -> Type)  *)
  (*   (Pset : forall (X : FSet A), IsHSet (P X)) *)
  (*   (Pempt : P ∅) *)
  (*   (Pcons : forall (a : A) (X : FSet A), P X -> P ({|a|} ∪ X)) *)
  (*   (Pdupl : forall (a : A) (X : FSet A) (px : P X), *)
  (*      transport P (dupl' a X) (Pcons a _ (Pcons a X px)) = Pcons a X px) *)
  (*   (Pcomm : forall (a b : A) (X : FSet A) (px : P X), *)
  (*      transport P (comm' a b X) (Pcons a _ (Pcons b X px)) = Pcons b _ (Pcons a X px)) : *)
  (*   forall a X, apD (FSet_cons_ind P Pset Pempt Pcons Pdupl Pcomm) (dupl' a X) = Pdupl a X (FSet_cons_ind P Pset Pempt Pcons Pdupl Pcomm X). *)
End Iso.
