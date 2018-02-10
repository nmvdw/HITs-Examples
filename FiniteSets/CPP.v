Require Import FSets list_representation.
Require Import kuratowski.length misc.dec_kuratowski.
From FSets.interfaces Require Import lattice_interface.
From FSets.subobjects Require Import sub b_finite enumerated k_finite.

(** * Definitions *)
Definition definition_2_1 := FSet.
Definition definition_2_2 := FSet_ind.
Definition lemma_2_3 {A : Type} : forall x: FSet A, x ∪ x = x := union_idem.

(** ** Extensionality *)
Definition definition_2_4 `{Univalence} := fset_member.
Definition theorem_2_5 `{Univalence} {A} (X Y : FSet A) :
    X = Y <~> forall (a : A), a ∈ X = a ∈ Y := fset_ext X Y.
Definition lemma_2_6 `{Univalence} (A : Type) (X Y : FSet A) := equiv_subset1_r X Y.

(** ** L(A) definition *)
Definition definition_2_7 := list_representation.FSetC.FSetC.
Definition theorem_2_8 {A} : FSet A <~> FSetC A := isomorphism.repr_iso.
Definition proposition_2_9 {A : Type} :
  forall P : Type,
    IsHSet P ->
    P ->
    forall Pcons : A -> FSet A -> P -> P,
      (forall (X : FSet A) (a : A) (p : P),
          Pcons a {|a|} ∪ X (Pcons a X p) = Pcons a X p) ->
      (forall (X : FSet A) (a b : A) (p : P),
          Pcons a {|b|} ∪ X (Pcons b X p) = Pcons b {|a|} ∪ X (Pcons a X p)) ->
      FSet A -> P
  := FSet_cons_rec.


(** * Decidability *)
Require Import misc.dec_lem.
Definition theorem_3_1 `{Univalence} := merely_dec.

(** ** Decidable membership *)
Definition proposition_3_2 `{Univalence} {A}
  `{MerelyDecidablePaths A}
  (x : FSet A) (a : A) :
  Decidable (a ∈ x)
  := isIn_decidable a x.
Definition definition_3_3 `{Univalence} {A}`{MerelyDecidablePaths A}
  := fset_member_bool.
Definition proposition_3_4 `{H: Univalence} {A : Type} := @dec_membership A H.

(** ** Size *)
Definition proposition_3_5 `{Univalence} (A: Type) `{MerelyDecidablePaths A}
 (X : FSet A) : nat := length X.
Definition proposition_3_6 `{H : Univalence} (A : Type) := @dec_length A H.

(** ** Lattice structure *)
Definition definition_3_7 := fset_comprehension.
Definition definition_3_8 `{H : Univalence} {A : Type}
 `{M : MerelyDecidablePaths A} := @fset_intersection A M H.
Definition proposition_3_9 `{H : Univalence} {A : Type}
 `{M : MerelyDecidablePaths A} (X Y : FSet A) := intersection_isIn X Y.
Definition theorem_3_10 {H : Univalence} {A : Type}
 `{M : MerelyDecidablePaths A} := @lattice_fset A M H.
Definition proposition_3_11 `{H : Univalence} (A : Type) := @merely_choice A H.
Definition proposition_3_12 `{H: Univalence} (A : Type) := @dec_intersection A H.


(** * Finite types *)
(** ** Subobjects *)
Definition definition_4_1 := Sub.
Definition lemma_4_2 := notIn_ext_union_singleton.
(** ** Bishop-finite *)
Definition definition_4_3 := Fin.
Definition definition_4_4 := Finite.
Definition definition_4_5 (A: Type) (X : Sub A) := Bfin X.
Definition lemma_4_6 := Finite_ind.
Definition proposition_4_7 := singleton.
Definition proposition_4_8 := set_singleton.

Definition lemma_4_9 `{Univalence} (A : Type) (P : Sub A) := split P.
Definition lemma_4_10 `{Univalence} := DecidableMembership.
Definition proposition_4_11 := bfin_union.
Definition proposition_4_12 := no_union.

(** ** Finite by enumeration *)
Definition definition_4_13 := enumerated.
Definition definition_4_14 := Kf. (* We define it slightly differently in Coq, see also lemma [Kf_unfold] *)
Definition proposition_4_15 := Kf_sub_hprop.
Definition proposition_4_16 := enumerated_Kf.
Definition proposition_4_17 `{Univalence} := Kf_enumerated.
Definition proposition_4_18 := map_injective.
Definition definition_4_19 := Kf_sub.
Definition example_4_20 `{Univalence} := S1_Kfinite.
Definition theorem_4_21 `{Univalence} (X Y : Type) :
  (forall (f : X -> Y), IsSurjection f -> Kf X -> Kf Y)
  /\ (Kf X -> Kf Y -> Kf (X * Y))
  /\ (Kf X -> Kf Y -> Kf (X + Y))
  /\ (closedSingleton (Kf_sub X))
  /\ (closedUnion (Kf_sub X)).
Proof.
  repeat split.
  - apply Kf_surjection.
  - apply Kf_prod.
  - apply Kf_sum.
  - apply k_finite_singleton.
  - apply k_finite_union.
Qed.
Definition proposition_4_22 `{Univalence} := bfin_to_kfin.
Definition theorem_4_23 `{Univalence} (X : Type) `{DecidablePaths X} := Kf_to_Bf X.

(** * Interface for finite sets *)
From FSets.interfaces Require Import set_interface.
(** ** Method *)
Definition definition_5_1 := tt. (* not actually present; bundled in the next definition *)
Definition definition_5_2 `{Univalence} := sets.
Definition proposition_5_3 `{Univalence} := f_surjective.
Definition proposition_5_4 `{Univalence} (T : Type -> Type)
  (f : forall A, T A -> FSet A) `{sets T f} (A : Type) := quotient_iso (f A).
Definition proposition_5_5 `{Univalence} := same_class.
Definition theorem_5_6 := transfer.
Definition corollary_5_7 := refinement.
(** ** Application *)
Require Import misc.dec_fset.
Definition definition_5_8 `{Univalence} {A : Type} (P : A -> hProp) := all P.
Definition proposition_5_9 `{Univalence} {A : Type} (P : A -> hProp) :
   (forall (x : FSet A), (forall (a : A), a ∈ x -> P a) -> all P x)
/\ (forall (x : FSet A) (a : A), all P x -> (a ∈ x) -> P a).
Proof.
  split.
  - apply all_intro.
  - apply all_elim.
Qed.

(** * Related work *)
(** This is not stated separately in the paper, but we can handle examples from e.g. "Denis Firsov and Tarmo Uustalu. 2015. Dependently Typed Program-
ming with Finite Sets" *)
(** The Pauli group example *)
Definition misc_1 `{Univalence} := Pauli_mult_comm.
(** Decidability of prediates on finite sets is preserved by quantifiers *)
Definition misc_2 `{Univalence} {A : Type} (P : A -> hProp) `{forall a, Decidable (P a)} := all_decidable P.
