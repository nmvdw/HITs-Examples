(* Logical disjunction in HoTT (see ch. 3 of the book) *)
Require Import HoTT.
Require Import lattice notation.

Instance lor : maximum hProp := fun X Y => BuildhProp (Trunc (-1) (sum X Y)).

Delimit Scope logic_scope with L.
Notation "A ∨ B" := (lor A B) (at level 20, right associativity) : logic_scope.
Arguments lor _%L _%L.
Open Scope logic_scope.

Section lor_props.
  Context `{Univalence}.
  Variable X Y Z : hProp.

  Local Ltac lor_intros :=
    let x := fresh in intro x
             ; repeat (strip_truncations ; destruct x as [x | x]).
  
  
  Lemma lor_assoc : (X ∨ Y) ∨ Z = X ∨ Y ∨ Z.
  Proof.
    apply path_iff_hprop ; lor_intros
    ; apply tr ; auto
    ; try (left ; apply tr)
    ; try (right ; apply tr) ; auto.
  Defined.  

  Lemma lor_comm : X ∨ Y = Y ∨ X.
  Proof.
    apply path_iff_hprop ; lor_intros
    ; apply tr ; auto.
  Defined.

  Lemma lor_nl : False_hp ∨ X = X.
  Proof.
    apply path_iff_hprop ; lor_intros ; try contradiction
    ; try (refine (tr(inr _))) ; auto.
  Defined.

  Lemma lor_nr : X ∨ False_hp = X.
  Proof.
    apply path_iff_hprop ; lor_intros ; try contradiction
    ; try (refine (tr(inl _))) ; auto.
  Defined.

  Lemma lor_idem : X ∨ X = X.
  Proof.
    apply path_iff_hprop ; lor_intros
    ; try(refine (tr(inl _))) ; auto.
  Defined.

End lor_props.

Instance land : minimum hProp := fun X Y => BuildhProp (prod X Y).
Instance lfalse : bottom hProp := False_hp.

Notation "A ∧ B" := (land A B) (at level 20, right associativity) : logic_scope.
Arguments land _%L _%L.
Open Scope logic_scope.

Section hPropLattice.
  Context `{Univalence}.

  Instance lor_commutative : Commutative lor.
  Proof.
    unfold Commutative.
    intros.
    apply lor_comm.
  Defined.

  Instance land_commutative : Commutative land.
  Proof.
    unfold Commutative, land.
    intros.
    apply path_hprop.
    apply equiv_prod_symm.
  Defined.

  Instance lor_associative : Associative lor.
  Proof.
    unfold Associative.
    intros.
    apply lor_assoc.
  Defined.

  Instance land_associative : Associative land.
  Proof.
    unfold Associative, land.
    intros.
    symmetry.
    apply path_hprop.
    apply equiv_prod_assoc.
  Defined.

  Instance lor_idempotent : Idempotent lor.
  Proof.
    unfold Idempotent.
    intros.
    apply lor_idem.
  Defined.

  Instance land_idempotent : Idempotent land.
  Proof.
    unfold Idempotent, land.
    intros.
    apply path_iff_hprop ; cbn.
    - intros [a b] ; apply a.
    - intros a ; apply (pair a a).
  Defined.

  Instance lor_neutrall : NeutralL lor lfalse.
  Proof.
    unfold NeutralL.
    intros.
    apply lor_nl.
  Defined.

  Instance lor_neutralr : NeutralR lor lfalse.
  Proof.
    unfold NeutralR.
    intros.
    apply lor_nr.
  Defined.

  Instance absorption_orb_andb : Absorption lor land.
  Proof.
    unfold Absorption.
    intros.
    apply path_iff_hprop ; cbn.
    - intros X ; strip_truncations.
      destruct X as [Xx | [Xy1 Xy2]] ; assumption.
    - intros X.
      apply (tr (inl X)).
  Defined.

  Instance absorption_andb_orb : Absorption land lor.
  Proof.
    unfold Absorption.
    intros.
    apply path_iff_hprop ; cbn.
    - intros [X Y] ; strip_truncations.
      assumption.
    - intros X.
      split.
      * assumption.
      * apply (tr (inl X)).
  Defined.

  Global Instance lattice_hprop : Lattice hProp :=
    { commutative_min := _ ;
      commutative_max := _ ;
      associative_min := _ ;
      associative_max := _ ;
      idempotent_min := _ ;
      idempotent_max := _ ;
      neutralL_max := _ ;
      neutralR_max := _ ;
      absorption_min_max := _ ;
      absorption_max_min := _
  }.

End hPropLattice.
