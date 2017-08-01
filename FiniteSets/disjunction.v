(* Logical disjunction in HoTT (see ch. 3 of the book) *)
Require Import HoTT.
Require Import lattice.

Definition lor (X Y : hProp) : hProp := BuildhProp (Trunc (-1) (sum X Y)).

Delimit Scope logic_scope with L.
Notation "A ∨ B" := (lor A B) (at level 20, right associativity) : logic_scope.
Arguments lor _%L _%L.
Open Scope logic_scope.

Section lor_props.
  Context `{Univalence}.
  Variable X Y Z : hProp.
  
  Lemma lor_assoc : (X ∨ Y) ∨ Z = X ∨ Y ∨ Z.
  Proof.
    apply path_iff_hprop ; cbn.
    * simple refine (Trunc_ind _ _).
      intros [xy | z] ; cbn.
      + simple refine (Trunc_ind _ _ xy).
        intros [x | y].
        ++ apply (tr (inl x)). 
        ++ apply (tr (inr (tr (inl y)))).
      + apply (tr (inr (tr (inr z)))).
    * simple refine (Trunc_ind _ _).    
      intros [x | yz] ; cbn.
      + apply (tr (inl (tr (inl x)))).
      + simple refine (Trunc_ind _ _ yz).
        intros [y | z].
        ++ apply (tr (inl (tr (inr y)))). 
        ++ apply (tr (inr z)).
  Defined.

  Lemma lor_comm : X ∨ Y = Y ∨ X.
  Proof.
    apply path_iff_hprop ; cbn.
    * simple refine (Trunc_ind _ _).
      intros [x | y].
      + apply (tr (inr x)).
      + apply (tr (inl y)).
    * simple refine (Trunc_ind _ _).
      intros [y | x].
      + apply (tr (inr y)).
      + apply (tr (inl x)).
  Defined.

  Lemma lor_nl : False_hp ∨ X = X.
  Proof.
    apply path_iff_hprop ; cbn.
    * simple refine (Trunc_ind _ _).
      intros [ | x].
      + apply Empty_rec.
      + apply x.
    * apply (fun x => tr (inr x)).
  Defined.

  Lemma lor_nr : X ∨ False_hp = X.
  Proof.
    apply path_iff_hprop ; cbn.
    * simple refine (Trunc_ind _ _).
      intros [x | ].
      + apply x.
      + apply Empty_rec.
    * apply (fun x => tr (inl x)).
  Defined.

  Lemma lor_idem : X ∨ X = X.
  Proof.
    apply path_iff_hprop ; cbn.
    - simple refine (Trunc_ind _ _).
      intros [x | x] ; apply x.
    - apply (fun x => tr (inl x)).
  Defined.

End lor_props.

Definition land (X Y : hProp) : hProp := BuildhProp (prod X Y).

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
  
  Instance lor_neutrall : NeutralL lor False_hp.
  Proof.
    unfold NeutralL.
    intros.
    apply lor_nl.
  Defined.

  Instance lor_neutralr : NeutralR lor False_hp.
  Proof.
    unfold NeutralR.
    intros.
    apply lor_nr.
  Defined.

  Instance bool_absorption_orb_andb : Absorption lor land.
  Proof.
    unfold Absorption.
    intros.
    apply path_iff_hprop ; cbn.
    - intros X ; strip_truncations.
      destruct X as [Xx | [Xy1 Xy2]] ; assumption.
    - intros X.
      apply (tr (inl X)).
  Defined.

  Instance bool_absorption_andb_orb : Absorption land lor.
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
  
  Global Instance lattice_hprop : Lattice land lor False_hp :=
    { commutative_min := _ ;
      commutative_max := _ ;
      associative_min := _ ;
      associative_max := _ ;
      idempotent_min := _ ;
      idempotent_max := _ ;
      neutralL_min := _ ;
      neutralR_min := _ ;
      absorption_min_max := _ ;
      absorption_max_min := _
  }.
  
End hPropLattice.

Hint Resolve
     commutative_min commutative_max associative_min associative_max
     idempotent_min idempotent_max
     neutralL_min neutralR_min
     absorption_min_max absorption_max_min
 : lattice_hints.