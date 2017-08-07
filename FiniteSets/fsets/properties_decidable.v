(* Properties of [FSet A] where [A] has decidable equality *)
Require Import HoTT HitTactics.
From fsets Require Export properties extensionality operations_decidable.
Require Export lattice.

(* Lemmas relating operations to the membership predicate *)
Section operations_isIn.

  Context {A : Type} `{DecidablePaths A} `{Univalence}.

  Lemma ext : forall (S T : FSet A), (forall a, isIn_b a S = isIn_b a T) -> S = T.
  Proof.
    intros X Y H2.
    apply fset_ext.
    intro a.
    specialize (H2 a).
    unfold isIn_b, dec in H2.
    destruct (isIn_decidable a X) ; destruct (isIn_decidable a Y).
    - apply path_iff_hprop ; intro ; assumption.
    - contradiction (true_ne_false).
    - contradiction (true_ne_false) ; apply H2^.
    - apply path_iff_hprop ; intro ; contradiction.
  Defined.

  Lemma empty_isIn (a : A) :
    isIn_b a ∅ = false.
  Proof.
    reflexivity.
  Defined.

  Lemma L_isIn (a b : A) :
    a ∈ {|b|} -> a = b.
  Proof.
    intros. strip_truncations. assumption.
  Defined.

  Lemma L_isIn_b_true (a b : A) (p : a = b) :
    isIn_b a {|b|} = true.
  Proof.
    unfold isIn_b, dec.
    destruct (isIn_decidable a {|b|}) as [n | n] .
    - reflexivity.
    - simpl in n.
      contradiction (n (tr p)).
  Defined.

  Lemma L_isIn_b_aa (a : A) :
    isIn_b a {|a|} = true.
  Proof.
    apply L_isIn_b_true ; reflexivity.
  Defined.

  Lemma L_isIn_b_false (a b : A) (p : a <> b) :
    isIn_b a {|b|} = false.
  Proof.
    unfold isIn_b, dec.
    destruct (isIn_decidable a {|b|}).
    - simpl in t.
      strip_truncations.
      contradiction.
    - reflexivity.
  Defined.
  
  (* Union and membership *)
  Lemma union_isIn_b (X Y : FSet A) (a : A) :
    isIn_b a (X ∪ Y) = orb (isIn_b a X) (isIn_b a Y).
  Proof.
    unfold isIn_b ; unfold dec.
    simpl.
    destruct (isIn_decidable a X) ; destruct (isIn_decidable a Y) ; reflexivity.
  Defined.

  Lemma comprehension_isIn_b (Y : FSet A) (ϕ : A -> Bool) (a : A) :
    isIn_b a (comprehension ϕ Y) = andb (isIn_b a Y) (ϕ a).
  Proof.
    unfold isIn_b, dec ; simpl.
    destruct (isIn_decidable a (comprehension ϕ Y)) as [t | t]
    ; destruct (isIn_decidable a Y) as [n | n] ; rewrite comprehension_isIn in t
    ; destruct (ϕ a) ; try reflexivity ; try contradiction.
  Defined.

  Lemma intersection_isIn_b (X Y: FSet A) (a : A) :
    isIn_b a (intersection X Y) = andb (isIn_b a X) (isIn_b a Y).
  Proof.
    apply comprehension_isIn_b.
  Defined.

End operations_isIn.

Global Opaque isIn_b.

(* Some suporting tactics *)
Ltac simplify_isIn :=
  repeat (rewrite union_isIn_b
        || rewrite L_isIn_b_aa
        || rewrite intersection_isIn_b
        || rewrite comprehension_isIn_b).

Ltac toBool :=
  repeat intro;
  apply ext ; intros ;
  simplify_isIn ; eauto with bool_lattice_hints typeclass_instances.

Section SetLattice.

  Context {A : Type}.
  Context {A_deceq : DecidablePaths A}.
  Context `{Univalence}.

  Instance fset_max : maximum (FSet A) := U.
  Instance fset_min : minimum (FSet A) := intersection.
  Instance fset_bot : bottom (FSet A) := ∅.
  
  Instance lattice_fset : Lattice (FSet A).
  Proof.
    split; toBool.
  Defined.
  
End SetLattice.

(* Comprehension properties *)
Section comprehension_properties.

  Context {A : Type}.
  Context {A_deceq : DecidablePaths A}.
  Context `{Univalence}.

  Lemma comprehension_or : forall ϕ ψ (x: FSet A),
      comprehension (fun a => orb (ϕ a) (ψ a)) x
      = U (comprehension ϕ x) (comprehension ψ x).
  Proof.
    toBool.
  Defined.
  
  (** comprehension properties *)
  Lemma comprehension_false Y : comprehension (fun (_ : A) => false) Y = ∅.
  Proof.
    toBool.
  Defined.

  Lemma comprehension_all : forall (X : FSet A),
      comprehension (fun a => isIn_b a X) X = X.
  Proof.
    toBool.
  Defined.
  
  Lemma comprehension_subset : forall ϕ (X : FSet A),
      (comprehension ϕ X) ∪ X = X.
  Proof.
    toBool.
  Defined.
  
End comprehension_properties.

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