Require Import HoTT HitTactics.
From fsets Require Import operations extensionality.
Require Export representations.definition disjunction.
Require Import lattice.

(* Lemmas relating operations to the membership predicate *)
Section characterize_isIn.
  Context {A : Type}.
  Context `{Univalence}.

  (** isIn properties *)
  Definition empty_isIn (a: A) : a ∈ ∅ -> Empty := idmap.

  Definition singleton_isIn (a b: A) : a ∈ {|b|} -> Trunc (-1) (a = b) := idmap.

  Definition union_isIn (X Y : FSet A) (a : A)
    : a ∈ X ∪ Y = a ∈ X ∨ a ∈ Y := idpath.

  Lemma comprehension_union (ϕ : A -> Bool) : forall X Y : FSet A,
      {|X ∪ Y & ϕ|} = {|X & ϕ|} ∪ {|Y & ϕ|}.
  Proof.
    reflexivity.
  Defined.

  Lemma comprehension_isIn (ϕ : A -> Bool) (a : A) : forall X : FSet A,
      a ∈ {|X & ϕ|} = if ϕ a then a ∈ X else False_hp.
  Proof.
    hinduction ; try (intros ; apply set_path2).
    - destruct (ϕ a) ; reflexivity.
    - intros b.
      assert (forall c d, ϕ a = c -> ϕ b = d ->
                          a ∈ (if ϕ b then {|b|} else ∅)
                          =
                          (if ϕ a then BuildhProp (Trunc (-1) (a = b)) else False_hp)) as X.
      {
        intros c d Hc Hd.
        destruct c ; destruct d ; rewrite Hc, Hd ; try reflexivity
        ; apply path_iff_hprop ; try contradiction ; intros ; strip_truncations
        ; apply (false_ne_true).
        * apply (Hd^ @ ap ϕ X^ @ Hc).
        * apply (Hc^ @ ap ϕ X @ Hd).
      }
      apply (X (ϕ a) (ϕ b) idpath idpath).
    - intros X Y H1 H2.
      rewrite comprehension_union.
      rewrite union_isIn.
      rewrite H1, H2.
      destruct (ϕ a).
      * reflexivity.
      * apply path_iff_hprop.
        ** intros Z ; strip_truncations.
           destruct Z ; assumption.
        ** intros ; apply tr ; right ; assumption.
  Defined.
End characterize_isIn.

Section product_isIn.
  Context {A B : Type}.
  Context `{Univalence}.

  Lemma isIn_singleproduct (a : A) (b : B) (c : A) : forall (Y : FSet B),
      (a, b) ∈ (single_product c Y) = land (BuildhProp (Trunc (-1) (a = c))) (b ∈ Y).
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - apply path_hprop ; symmetry ; apply prod_empty_r.
    - intros d.
      apply path_iff_hprop.
      * intros.
        strip_truncations.
        split ; apply tr ; try (apply (ap fst X)) ; try (apply (ap snd X)).
      * intros [Z1 Z2].
        strip_truncations.
        rewrite Z1, Z2.
        apply (tr idpath).
    - intros X1 X2 HX1 HX2.
      apply path_iff_hprop ; rewrite ?union_isIn.
      * intros X.
        strip_truncations.
        destruct X as [H1 | H1] ; rewrite ?HX1, ?HX2 in H1 ; destruct H1 as [H1 H2].
        ** split.
           *** apply H1.
           *** apply (tr(inl H2)).
        ** split.
           *** apply H1.
           *** apply (tr(inr H2)).
      * intros [H1 H2].
        strip_truncations.
        apply tr.
        rewrite HX1, HX2.
        destruct H2 as [Hb1 | Hb2].
        ** left.
           split ; try (apply (tr H1)) ; try (apply Hb1).
        ** right.
           split ; try (apply (tr H1)) ; try (apply Hb2).
  Defined.

  Definition isIn_product (a : A) (b : B) (X : FSet A) (Y : FSet B) :
    (a,b) ∈ (product X Y) = land (a ∈ X) (b ∈ Y).
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - apply path_hprop ; symmetry ; apply prod_empty_l.
    - intros.
      apply isIn_singleproduct.
    - intros X1 X2 HX1 HX2.
      rewrite (union_isIn (product X1 Y)).
      rewrite HX1, HX2.
      apply path_iff_hprop ; rewrite ?union_isIn.
      * intros X.
        strip_truncations.
        destruct X as [[H3 H4] | [H3 H4]] ; split ; try (apply H4).
        ** apply (tr(inl H3)).
        ** apply (tr(inr H3)).
      * intros [H1 H2].
        strip_truncations.
        destruct H1 as [H1 | H1] ; apply tr.
        ** left ; split ; assumption.
        ** right ; split ; assumption.
  Defined.
End product_isIn.

Ltac simplify_isIn :=
  repeat (rewrite union_isIn
          || rewrite comprehension_isIn).

Ltac toHProp :=
  repeat intro;
  apply fset_ext ; intros ;
  simplify_isIn ; eauto with lattice_hints typeclass_instances.

(* Other properties *)
Section properties.
  Context {A : Type}.
  Context `{Univalence}.

  Instance: bottom(FSet A).
  Proof.
    unfold bottom.
    apply ∅.
  Defined.

  Instance: maximum(FSet A).
  Proof.
    intros x y.
    apply (x ∪ y).
  Defined.

  Global Instance joinsemilattice_fset : JoinSemiLattice (FSet A).
  Proof.
    split ; toHProp.
  Defined.

  (** comprehension properties *)
  Lemma comprehension_false : forall (X : FSet A), {|X & fun _ => false|} = ∅.
  Proof.
    toHProp.
  Defined.

  Lemma comprehension_subset : forall ϕ (X : FSet A),
      {|X & ϕ|} ∪ X = X.
  Proof.
    toHProp.
    destruct (ϕ a) ; eauto with lattice_hints typeclass_instances.
  Defined.

  Lemma comprehension_or : forall ϕ ψ (X : FSet A),
      {|X & (fun a => orb (ϕ a) (ψ a))|}
      = {|X & ϕ|} ∪ {|X & ψ|}.
  Proof.
    toHProp.
    symmetry ; destruct (ϕ a) ; destruct (ψ a)
    ; eauto with lattice_hints typeclass_instances.
  Defined.

  Lemma comprehension_all : forall (X : FSet A),
      {|X & fun _ => true|} = X.
  Proof.
    toHProp.
  Defined.

  Lemma merely_choice : forall X : FSet A, hor (X = ∅) (hexists (fun a => a ∈ X)).
  Proof.
    hinduction; try (intros; apply equiv_hprop_allpath ; apply _).
    - apply (tr (inl idpath)).
    - intro a.
      refine (tr (inr (tr (a ; tr idpath)))).
    - intros X Y TX TY.
      strip_truncations.
      destruct TX as [XE | HX] ; destruct TY as [YE | HY] ; try(strip_truncations ; apply tr).
      * refine (tr (inl _)).
        rewrite XE, YE.
        apply (union_idem ∅).
      * destruct HY as [a Ya].
        refine (inr (tr _)).
        exists a.
        apply (tr (inr Ya)).
      * destruct HX as [a Xa].
        refine (inr (tr _)).
        exists a.
        apply (tr (inl Xa)).
      * destruct (HX, HY) as [[a Xa] [b Yb]].
        refine (inr (tr _)).
        exists a.
        apply (tr (inl Xa)).
  Defined.

  Lemma separation_isIn (B : Type) : forall (X : FSet A) (f : {a | a ∈ X} -> B) (b : B),
      b ∈ (separation A B X f) = hexists (fun a : A => hexists (fun (p : a ∈ X) => f (a;p) = b)).
  Proof.
    hinduction ; try (intros ; apply path_forall ; intro ; apply path_ishprop).
    - intros ; simpl.
      apply path_iff_hprop ; try contradiction.
      intros X.
      strip_truncations.
      destruct X as [a X].
      strip_truncations.
      destruct X as [p X].
      assumption.
    - intros.
      apply path_iff_hprop ; simpl.
      * intros ; strip_truncations.
        apply tr.
        exists a.
        apply tr.
        exists (tr idpath).
        apply X^.
      * intros X ; strip_truncations.
        destruct X as [a0 X].
        strip_truncations.
        destruct X as [X q].
        simple refine (Trunc_ind _ _ X).
        intros p.
        apply tr.
        rewrite <- q.
        f_ap.
        simple refine (path_sigma _ _ _ _ _).
        ** apply p.
        ** apply path_ishprop.
    - intros X1 X2 HX1 HX2 f b.
      pose (fX1 := fun Z : {a : A & a ∈ X1} => f (pr1 Z;tr (inl (pr2 Z)))).
      pose (fX2 := fun Z : {a : A & a ∈ X2} => f (pr1 Z;tr (inr (pr2 Z)))).
      specialize (HX1 fX1 b).
      specialize (HX2 fX2 b).
      apply path_iff_hprop.
      * intros X.
        rewrite union_isIn in X.
        strip_truncations.
        destruct X as [X | X].
        ** rewrite HX1 in X.
           strip_truncations.
           destruct X as [a Ha].
           apply tr.
           exists a.
           strip_truncations.
           destruct Ha as [p pa].
           apply tr.
           exists (tr(inl p)).
           rewrite <- pa.
           reflexivity.
        ** rewrite HX2 in X.
           strip_truncations.
           destruct X as [a Ha].
           apply tr.
           exists a.
           strip_truncations.
           destruct Ha as [p pa].
           apply tr.
           exists (tr(inr p)).
           rewrite <- pa.
           reflexivity.
      * intros.
        strip_truncations.
        destruct X as [a X].
        strip_truncations.
        destruct X as [Ha p].
        rewrite union_isIn.
        simple refine (Trunc_ind _ _ Ha) ; intros [Ha1 | Ha2].
        ** refine (tr(inl _)).
           rewrite HX1.
           apply tr.
           exists a.
           apply tr.
           exists Ha1.
           rewrite <- p.
           unfold fX1.
           repeat f_ap.
           apply path_ishprop.
        ** refine (tr(inr _)).
           rewrite HX2.
           apply tr.
           exists a.
           apply tr.
           exists Ha2.
           rewrite <- p.
           unfold fX2.
           repeat f_ap.
           apply path_ishprop.
  Defined.

End properties.
