Require Import HoTT HitTactics prelude.
Require Import kuratowski.extensionality kuratowski.operations kuratowski_sets.
Require Import lattice_interface lattice_examples monad_interface.

(** Lemmas relating operations to the membership predicate *)
Section properties_membership.
  Context {A : Type} `{Univalence}.

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

  Context {B : Type}.

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
        cbn in *.
        strip_truncations.
        destruct X as [H1 | H1] ; rewrite ?HX1, ?HX2 in H1
        ; destruct H1 as [H1 H2].
        ** split.
           *** apply H1.
           *** apply (tr(inl H2)).
        ** split.
           *** apply H1.
           *** apply (tr(inr H2)).
      * intros [H1 H2].
        cbn in *.
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
      cbn.
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
  
  Lemma separation_isIn : forall (X : FSet A) (f : {a | a ∈ X} -> B) (b : B),
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
        cbn in *.
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
        cbn.
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
End properties_membership.

Ltac simplify_isIn :=
  repeat (rewrite union_isIn
          || rewrite comprehension_isIn).

Ltac toHProp :=
  repeat intro;
  apply fset_ext ; intros ;
  simplify_isIn ; eauto with lattice_hints typeclass_instances.

(** [FSet A] is a join semilattice. *)
Section fset_join_semilattice.
  Context {A : Type}.

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
    split.
    - intros ? ?.
      apply comm.
    - intros ? ? ?.
      apply (assoc _ _ _)^.
    - intros ?.
      apply union_idem.
    - intros x.
      apply nl.
    - intros ?.
      apply nr.
  Defined.
End fset_join_semilattice.

(* Lemmas relating operations to the membership predicate *)
Section properties_membership_decidable.
  Context {A : Type} `{MerelyDecidablePaths A} `{Univalence}.

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

  Definition empty_isIn_d (a : A) : a ∈_d ∅ = false := idpath.

  Lemma singleton_isIn_d_true (a b : A) (p : a = b) :
    a ∈_d {|b|} = true.
  Proof.
    unfold member_dec, fset_member_bool, dec.
    destruct (isIn_decidable a {|b|}) as [n | n] .
    - reflexivity.
    - simpl in n.
      contradiction (n (tr p)).
  Defined.

  Lemma singleton_isIn_d_aa (a : A) :
    a ∈_d {|a|} = true.
  Proof.
    apply singleton_isIn_d_true ; reflexivity.
  Defined.

  Lemma singleton_isIn_d_false (a b : A) (p : a <> b) :
    a ∈_d {|b|} = false.
  Proof.
    unfold member_dec, fset_member_bool, dec in *.
    destruct (isIn_decidable a {|b|}).
    - simpl in t.
      strip_truncations.
      contradiction.
    - reflexivity.
  Defined.

  Lemma union_isIn_d (X Y : FSet A) (a : A) :
    a ∈_d (X ∪ Y) = orb (a ∈_d X) (a ∈_d Y).
  Proof.
    unfold member_dec, fset_member_bool, dec.
    simpl.
    destruct (isIn_decidable a X) ; destruct (isIn_decidable a Y) ; reflexivity.
  Defined.

  Lemma comprehension_isIn_d (Y : FSet A) (ϕ : A -> Bool) (a : A) :
    a ∈_d {|Y & ϕ|} = andb (a ∈_d Y) (ϕ a).
  Proof.
    unfold member_dec, fset_member_bool, dec ; simpl.
    destruct (isIn_decidable a {|Y & ϕ|}) as [t | t]
    ; destruct (isIn_decidable a Y) as [n | n] ; rewrite comprehension_isIn in t
    ; destruct (ϕ a) ; try reflexivity ; try contradiction
    ; try (contradiction (n t)) ; contradiction (t n).
  Defined.

  Lemma intersection_isIn_d (X Y: FSet A) (a : A) :
    a ∈_d (intersection X Y) = andb (a ∈_d X) (a ∈_d Y).
  Proof.
    apply comprehension_isIn_d.
  Defined.
  
  Lemma singleton_isIn_d `{IsHSet A} (a b : A) :
    a ∈ {|b|} -> a = b.
  Proof.
    intros.
    strip_truncations.
    assumption.
  Defined.
End properties_membership_decidable.

(* Some suporting tactics *)
Ltac simplify_isIn_d :=
  repeat (rewrite union_isIn_d
        || rewrite singleton_isIn_d_aa
        || rewrite intersection_isIn_d
        || rewrite comprehension_isIn_d).

Ltac toBool :=
  repeat intro;
  apply ext ; intros ;
  simplify_isIn_d ; eauto with bool_lattice_hints typeclass_instances.

(** If `A` has decidable equality, then `FSet A` is a lattice *) 
Section set_lattice.
  Context {A : Type}.
  Context `{MerelyDecidablePaths A}.
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
    split ; toBool.
  Defined.
End set_lattice.

(** If `A` has decidable equality, then so has `FSet A`. *)
Section dec_eq.
  Context {A : Type} `{DecidablePaths A} `{Univalence}.

  Instance fsets_dec_eq : DecidablePaths (FSet A).
  Proof.
    intros X Y.
    apply (decidable_equiv' ((Y ⊆ X) * (X ⊆ Y)) (eq_subset X Y)^-1).
    apply decidable_prod.
  Defined.
End dec_eq.

(** [FSet] is a (strong and stable) finite powerset monad *)
Section monad_fset.
  Context `{Funext}.

  Global Instance fset_functorish : Functorish FSet.
  Proof.
    simple refine (Build_Functorish _ _ _).
    - intros ? ? f.
      apply (fset_fmap f).
    - intros A.
      apply path_forall.
      intro x.
      hinduction x
      ; try (intros ; f_ap)
      ; try (intros ; apply path_ishprop).
  Defined.

  Global Instance fset_functor : Functor FSet.
  Proof.
    split.
    intros.
    apply path_forall.
    intro x.
    hrecursion x
    ; try (intros ; f_ap)
    ; try (intros ; apply path_ishprop).
  Defined.

  Global Instance fset_monad : Monad FSet.
  Proof.
    split.
    - intros.
      apply path_forall.
      intro X.
      hrecursion X ; try (intros; f_ap) ;
        try (intros; apply path_ishprop).
    - intros.
      apply path_forall.
      intro X.
      hrecursion X ; try (intros; f_ap) ;
        try (intros; apply path_ishprop).
    - intros.
      apply path_forall.
      intro X.
      hrecursion X ; try (intros; f_ap) ;
        try (intros; apply path_ishprop).
  Defined.

  Lemma fmap_isIn `{Univalence} {A B : Type} (f : A -> B) (a : A) (X : FSet A) :
    a ∈ X -> (f a) ∈ (fmap FSet f X).
  Proof.
    hinduction X; try (intros; apply path_ishprop).
    - apply idmap.
    - intros b Hab; strip_truncations.
      apply (tr (ap f Hab)).
    - intros X0 X1 HX0 HX1 Ha.
      strip_truncations. apply tr.
      destruct Ha as [Ha | Ha].
      + left. by apply HX0.
      + right. by apply HX1.
  Defined.
End monad_fset.

(** comprehension properties *)
Section comprehension_properties.
  Context {A : Type} `{Univalence}.

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
End comprehension_properties.

(** For [FSet A] we have mere choice. *)
Section mere_choice.
  Context {A : Type} `{Univalence}.

  Local Ltac solve_mc :=
    repeat (let x := fresh in intro x ; try(destruct x))
    ; simpl
    ; rewrite transport_sum
    ; try (f_ap ; apply path_ishprop)
    ; try (f_ap ; apply set_path2).

  Lemma merely_choice : forall X : FSet A, (X = ∅) + (hexists (fun a => a ∈ X)).
  Proof.
    hinduction.
    - apply (inl idpath).
    - intro a.
      refine (inr (tr (a ; tr idpath))).
    - intros X Y TX TY.
      destruct TX as [XE | HX] ; destruct TY as [YE | HY].
      * refine (inl _).
        rewrite XE, YE.
        apply (union_idem ∅).
      * right.
        strip_truncations.
        destruct HY as [a Ya].
        refine (tr _).
        exists a.
        apply (tr (inr Ya)).
      * right.
        strip_truncations.
        destruct HX as [a Xa].
        refine (tr _).
        exists a.
        apply (tr (inl Xa)).
      * right.
        strip_truncations.
        destruct (HX, HY) as [[a Xa] [b Yb]].
        refine (tr _).
        exists a.
        apply (tr (inl Xa)).
    - solve_mc.
    - solve_mc.
    - solve_mc.
    - solve_mc.
    - solve_mc.
  Defined.
End mere_choice.
