(** Extensionality of the FSets *)
Require Import HoTT HitTactics.
Require Import kuratowski.kuratowski_sets.

(** We prove extensionality via a chain of equivalences.
    We end with proving that equality can be defined with the subset relation.
    From that we can conclude that [FSet A] has decidable equality if [A] has.
*)
Section ext.
  Context {A : Type}.
  Context `{Univalence}.

  Lemma equiv_subset1_l (X Y : FSet A) (H1 : Y ∪ X = X) (a : A) (Ya : a ∈ Y) : a ∈ X.
  Proof.
    apply (transport (fun Z => a ∈ Z) H1 (tr(inl Ya))).
  Defined.
  
  Lemma equiv_subset1_r X : forall (Y : FSet A), (forall a, a ∈ Y -> a ∈ X) -> Y ∪ X = X.
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - intros.
      apply nl.
    - intros b sub.
      specialize (sub b (tr idpath)).
      revert sub.
      hinduction X ; try (intros ; apply path_ishprop).
      * contradiction.
      * intros.
        strip_truncations.
        rewrite sub.
        apply union_idem.
      * intros X Y subX subY mem.
        strip_truncations.
        destruct mem as [t | t].
        ** rewrite assoc, (subX t).
           reflexivity.
        ** rewrite (comm X), assoc, (subY t).
           reflexivity.
    - intros Y1 Y2 H1 H2 H3.
      rewrite <- assoc.
      rewrite (H2 (fun a HY => H3 a (tr(inr HY)))).
      apply (H1 (fun a HY => H3 a (tr(inl HY)))).
  Defined.

  Lemma eq_subset1 X Y : (Y ∪ X = X) * (X ∪ Y = Y) <~> forall (a : A), a ∈ X = a ∈ Y.
  Proof.    
    eapply equiv_iff_hprop_uncurried ; split.
    - intros [H1 H2] a.
      apply path_iff_hprop ; apply equiv_subset1_l ; assumption.
    - intros H1.
      split ; apply equiv_subset1_r ; intros.
      * rewrite H1 ; assumption.
      * rewrite <- H1 ; assumption.
  Defined.

  Lemma eq_subset2 (X Y : FSet A) : X = Y <~> (Y ∪ X = X) * (X ∪ Y = Y).
  Proof.
    eapply equiv_iff_hprop_uncurried ; split.
    - intro Heq.
      split.
      * apply (ap (fun Z => Z ∪ X) Heq^ @ union_idem X).
      * apply (ap (fun Z => Z ∪ Y) Heq @ union_idem Y).
    - intros [H1 H2].
      apply (H1^ @ comm Y X @ H2).
  Defined.
  
  Theorem fset_ext (X Y : FSet A) :
    X = Y <~> forall (a : A), a ∈ X = a ∈ Y.
  Proof.
    apply (equiv_compose' (eq_subset1 X Y) (eq_subset2 X Y)).
  Defined.

  Lemma subset_union (X Y : FSet A) :
    X ⊆ Y -> X ∪ Y = Y.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop). 
    - intros.
      apply nl.
    - intros a.
      hinduction Y ; try (intros ; apply path_ishprop).
      + intro.
        contradiction.
      + intros b p.
        strip_truncations.
        rewrite p.
        apply idem.
      + intros X1 X2 IH1 IH2 t.
        strip_truncations.
        destruct t as [t | t].
        ++ rewrite assoc, (IH1 t).
           reflexivity.
        ++ rewrite comm, <- assoc, (comm X2), (IH2 t).
           reflexivity.
    - intros X1 X2 IH1 IH2 [G1 G2].
      rewrite <- assoc.
      rewrite (IH2 G2).
      apply (IH1 G1).
  Defined.

  Lemma subset_union_l (X : FSet A) :
    forall Y, X ⊆ X ∪ Y.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - apply (fun _ => tt).
    - intros.
      apply (tr(inl(tr idpath))).
    - intros X1 X2 HX1 HX2 Y.
      split ; unfold subset in *.
      * rewrite <- assoc.
        apply HX1.
      * rewrite (comm X1 X2), <- assoc.
        apply HX2.
  Defined.

  Lemma subset_union_equiv
    : forall X Y : FSet A, X ⊆ Y <~> X ∪ Y = Y.
  Proof.
    intros X Y.
    eapply equiv_iff_hprop_uncurried.
    split.
    - apply subset_union.
    - intro HXY.
      rewrite <- HXY.
      apply subset_union_l.
  Defined.
  
  Lemma subset_isIn (X Y : FSet A) :
    X ⊆ Y <~> forall (a : A), a ∈ X -> a ∈ Y.
  Proof.
    etransitivity.
    - apply subset_union_equiv.
    - eapply equiv_iff_hprop_uncurried ; split.
      * apply equiv_subset1_l.
      * apply equiv_subset1_r.
  Defined.

  Lemma eq_subset (X Y : FSet A) :
    X = Y <~> (Y ⊆ X * X ⊆ Y).
  Proof.
    etransitivity ((Y ∪ X = X) * (X ∪ Y = Y)).
    - apply eq_subset2.
    - symmetry.
      eapply equiv_functor_prod' ; apply subset_union_equiv.
  Defined.
End ext.
