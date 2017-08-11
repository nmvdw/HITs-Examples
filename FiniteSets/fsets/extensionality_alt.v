(** Extensionality of the FSets *)
Require Import HoTT HitTactics.
Require Import representations.definition fsets.operations.

Section ext.
  Context {A : Type}.
  Context `{Univalence}.

  Lemma equiv_subset_l : forall (X Y : FSet A), Y ∪ X = X -> forall a, a ∈ Y -> a ∈ X.
  Proof.
    intros X Y H1 a Ya.
    rewrite <- H1.
    apply (tr(inl Ya)).
  Defined.

  Lemma equiv_subset_r : forall (X Y : FSet A), (forall a, a ∈ Y -> a ∈ X) -> Y ∪ X = X.
  Proof.
    intros X.
    hinduction ; try (intros ; apply path_forall ; intro ; apply path_ishprop).
    - intros.
      apply nl.
    - intros b sub.
      specialize (sub b (tr idpath)).
      revert sub.
      hinduction X ; try (intros ; apply path_forall ; intro ; apply path_ishprop).
      * contradiction.
      * intros.
        strip_truncations.
        rewrite sub.
        apply union_idem.
      * intros X Y subX subY mem.
        strip_truncations.
        destruct mem.
        ** rewrite assoc.
           rewrite (subX t).
           reflexivity.
        ** rewrite (comm X).
           rewrite assoc.
           rewrite (subY t).
           reflexivity.
    - intros Y1 Y2 H1 H2 H3.
      rewrite <- assoc.
      rewrite (H2 (fun a HY => H3 a (tr(inr HY)))).
      rewrite (H1 (fun a HY => H3 a (tr(inl HY)))).
      reflexivity.
  Defined.        

  Lemma eq_subset' (X Y : FSet A) : X = Y <~> (Y ∪ X = X) * (X ∪ Y = Y).
  Proof.
    unshelve eapply BuildEquiv.
    { intro H'. rewrite H'. split; apply union_idem. }
    unshelve esplit.
    { intros [H1 H2]. etransitivity. apply H1^.
      rewrite comm. apply H2. }
    intro; apply path_prod; apply set_path2.
    all: intro; apply set_path2.
  Defined.
  
  Theorem fset_ext (X Y : FSet A) :
    X = Y <~> (forall (a : A), a ∈ X = a ∈ Y).
  Proof.
    refine (@equiv_compose' _ _ _ _ _) ; [ | apply eq_subset' ].
    eapply equiv_iff_hprop_uncurried ; split.
    - intros [H1 H2 a].
      apply path_iff_hprop ; apply equiv_subset_l ; assumption.
    - intros H1.
      split ; apply equiv_subset_r.
      * intros a Ya.
        rewrite (H1 a) ; assumption.
      * intros a Xa.
        rewrite <- (H1 a) ; assumption.
  Defined.

End ext.