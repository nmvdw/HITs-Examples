(** Extensionality of the FSets *)
Require Import HoTT HitTactics.
From representations Require Import definition.
From fsets Require Import operations properties.

Section ext.
  Context {A : Type}.
  Context `{Univalence}.

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
    (forall (a : A), a ∈ X -> a ∈ Y)
      <~> (X ⊆ Y).
  Proof.
    eapply equiv_iff_hprop_uncurried.
    split.
    - hinduction X ;
        try (intros; repeat (apply path_forall; intro); apply equiv_hprop_allpath ; apply _).
      + intros ; reflexivity.
      + intros a f.
        apply f.
        apply tr ; reflexivity.
      + intros X1 X2 H1 H2 f.
        enough (X1 ⊆ Y).
        enough (X2 ⊆ Y).
        { split. apply X. apply X0. }
        * apply H2.
          intros a Ha.
          refine (f _ (tr _)).
          right.
          apply Ha.
        * apply H1.
          intros a Ha.
          refine (f _ (tr _)).
          left.
          apply Ha.
    - hinduction X ;
        try (intros; repeat (apply path_forall; intro); apply equiv_hprop_allpath ; apply _).
      + intros. contradiction.
      + intros b f a.
        simple refine (Trunc_ind _ _) ; cbn.
        intro p.
        rewrite p^ in f.
        apply f.
      + intros X1 X2 IH1 IH2 [H1 H2] a.
        simple refine (Trunc_ind _ _) ; cbn.
        intros [C1 | C2].
        ++ apply (IH1 H1 a C1).
        ++ apply (IH2 H2 a C2).
  Defined.

  (** ** Extensionality proof *)

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

  Lemma eq_subset (X Y : FSet A) :
    X = Y <~> (Y ⊆ X * X ⊆ Y).
  Proof.
    transitivity ((Y ∪ X = X) * (X ∪ Y = Y)).
    apply eq_subset'.
    symmetry.
    eapply equiv_functor_prod'; apply subset_union_equiv.
  Defined.

  Theorem fset_ext (X Y : FSet A) :
    X = Y <~> (forall (a : A), a ∈ X = a ∈ Y).
  Proof.
    refine (@equiv_compose' _ _ _ _ _) ; [ | apply eq_subset ].
    refine (@equiv_compose' _ ((forall a, a ∈ Y -> a ∈ X)
                               *(forall a, a ∈ X -> a ∈ Y)) _ _ _).
    - apply equiv_iff_hprop_uncurried.
      split.
      * intros [H1 H2 a].
        specialize (H1 a) ; specialize (H2 a).
        apply path_iff_hprop.
        apply H2.
        apply H1.
      * intros H1.
        split ; intro a ; intro H2.
      + rewrite (H1 a).
        apply H2.
      + rewrite <- (H1 a).
        apply H2.
    - eapply equiv_functor_prod' ;
        apply equiv_iff_hprop_uncurried ;
        split ; apply subset_isIn.
  Defined.

End ext.
