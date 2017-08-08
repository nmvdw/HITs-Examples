(* Properties of [FSet A] where [A] has decidable equality *)
Require Import HoTT HitTactics.
From fsets Require Export properties extensionality operations_decidable.
Require Export lattice.

(* Lemmas relating operations to the membership predicate *)
Section operations_isIn.

  Context {A : Type} `{DecidablePaths A} `{Univalence}.

  Lemma ext : forall (S T : FSet A), (forall a, a ∈_d S = a ∈_d T) -> S = T.
  Proof.
    intros X Y H2.
    apply fset_ext.
    intro a.
    specialize (H2 a).
    unfold member_dec, fset_member_bool, dec in H2.
    destruct (isIn_decidable a X) ; destruct (isIn_decidable a Y).
    - apply path_iff_hprop ; intro ; assumption.
    - contradiction (true_ne_false).
    - contradiction (true_ne_false) ; apply H2^.
    - apply path_iff_hprop ; intro ; contradiction.
  Defined.

  Lemma empty_isIn (a : A) :
    a ∈_d ∅ = false.
  Proof.
    reflexivity.
  Defined.

  Lemma L_isIn (a b : A) :
    a ∈ {|b|} -> a = b.
  Proof.
    intros. strip_truncations. assumption.
  Defined.

  Lemma L_isIn_b_true (a b : A) (p : a = b) :
    a ∈_d {|b|} = true.
  Proof.
    unfold member_dec, fset_member_bool, dec.
    destruct (isIn_decidable a {|b|}) as [n | n] .
    - reflexivity.
    - simpl in n.
      contradiction (n (tr p)).
  Defined.

  Lemma L_isIn_b_aa (a : A) :
    a ∈_d {|a|} = true.
  Proof.
    apply L_isIn_b_true ; reflexivity.
  Defined.

  Lemma L_isIn_b_false (a b : A) (p : a <> b) :
    a ∈_d {|b|} = false.
  Proof.
    unfold member_dec, fset_member_bool, dec in *.
    destruct (isIn_decidable a {|b|}).
    - simpl in t.
      strip_truncations.
      contradiction.
    - reflexivity.
  Defined.
  
  (* Union and membership *)
  Lemma union_isIn_b (X Y : FSet A) (a : A) :
    a ∈_d (X ∪ Y) = orb (a ∈_d X) (a ∈_d Y).
  Proof.
    unfold member_dec, fset_member_bool, dec.
    simpl.
    destruct (isIn_decidable a X) ; destruct (isIn_decidable a Y) ; reflexivity.
  Defined.

  Lemma comprehension_isIn_b (Y : FSet A) (ϕ : A -> Bool) (a : A) :
    a ∈_d {|Y & ϕ|} = andb (a ∈_d Y) (ϕ a).
  Proof.
    unfold member_dec, fset_member_bool, dec ; simpl.
    destruct (isIn_decidable a {|Y & ϕ|}) as [t | t]
    ; destruct (isIn_decidable a Y) as [n | n] ; rewrite comprehension_isIn in t
    ; destruct (ϕ a) ; try reflexivity ; try contradiction
    ; try (contradiction (n t)) ; contradiction (t n).
  Defined.

  Lemma intersection_isIn_b (X Y: FSet A) (a : A) :
    a ∈_d (intersection X Y) = andb (a ∈_d X) (a ∈_d Y).
  Proof.
    apply comprehension_isIn_b.
  Defined.

End operations_isIn.

(* Some suporting tactics *)
Ltac simplify_isIn_b :=
  repeat (rewrite union_isIn_b
        || rewrite L_isIn_b_aa
        || rewrite intersection_isIn_b
        || rewrite comprehension_isIn_b).

Ltac toBool :=
  repeat intro;
  apply ext ; intros ;
  simplify_isIn_b ; eauto with bool_lattice_hints typeclass_instances.

Section SetLattice.

  Context {A : Type}.
  Context {A_deceq : DecidablePaths A}.
  Context `{Univalence}.

  Instance fset_max : maximum (FSet A).
  Proof.
    intros x y.
    apply (x ∪ y).
  Defined.
      
  Instance fset_min : minimum (FSet A).
  Proof.
    intros x y.
    apply (x ∩ y).
  Defined.
  
  Instance fset_bot : bottom (FSet A).
  Proof.
    unfold bottom.
    apply ∅.
  Defined.
    
  Instance lattice_fset : Lattice (FSet A).
  Proof.
    split; toBool.
  Defined.
  
End SetLattice.

(* With extensionality we can prove decidable equality *)
Section dec_eq.
  Context (A : Type) `{DecidablePaths A} `{Univalence}.

  Instance fsets_dec_eq : DecidablePaths (FSet A).
  Proof.
    intros X Y.
    apply (decidable_equiv' ((Y ⊆ X) * (X ⊆ Y)) (eq_subset X Y)^-1).
    apply decidable_prod.
  Defined.

End dec_eq.