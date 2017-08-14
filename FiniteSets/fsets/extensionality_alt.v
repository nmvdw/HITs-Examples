(** Extensionality of the FSets *)
Require Import HoTT HitTactics.
Require Import representations.definition fsets.operations.

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
End ext.