Require Import HoTT HitTactics.
Require Import lattice representations.definition fsets.operations extensionality Sub fsets.properties fsets.monad.

Section k_finite.

  Context (A : Type).
  Context `{Univalence}.

  Definition map (X : FSet A) : Sub A := fun a => a ∈ X.

  Global Instance map_injective : IsEmbedding map.
  Proof.
    apply isembedding_isinj_hset. (* We use the fact that both [FSet A] and [Sub A] are hSets *)
    intros X Y HXY.
    apply fset_ext.
    apply apD10. exact HXY.
  Defined.

  Definition Kf_sub_intern (B : Sub A) := exists (X : FSet A), B = map X.

  Instance Kf_sub_hprop B : IsHProp (Kf_sub_intern B).
  Proof.
    apply hprop_allpath.
    intros [X PX] [Y PY].
    assert (X = Y) as HXY.
    { apply fset_ext. apply apD10.
      transitivity B; [ symmetry | ]; assumption. }
    apply path_sigma with HXY. simpl.
    apply set_path2.
  Defined.

  Definition Kf_sub (B : Sub A) : hProp := BuildhProp (Kf_sub_intern B).

  Definition Kf : hProp := Kf_sub (fun x => True).

  Instance: IsHProp {X : FSet A & forall a : A, map X a}.
  Proof.
    apply hprop_allpath.
    intros [X PX] [Y PY].
    assert (X = Y) as HXY.
    { apply fset_ext. intros a.
      unfold map in *.
      apply path_hprop.
      apply equiv_iff_hprop; intros.
      + apply PY.
      + apply PX. }
    apply path_sigma with HXY. simpl.
    apply path_forall. intro.
    apply path_ishprop.
  Defined.

  Lemma Kf_unfold : Kf <~> (exists (X : FSet A), forall (a : A), map X a).
  Proof.
    apply equiv_equiv_iff_hprop. apply _. apply _.
    split.
    - intros [X PX]. exists X. intro a.
      rewrite <- PX. done.
    - intros [X PX]. exists X. apply path_forall; intro a.
      apply path_hprop.
      symmetry. apply if_hprop_then_equiv_Unit; [ apply _ | ].
      apply PX.
  Defined.

End k_finite.

Arguments map {_} {_} _.

Section structure_k_finite.
  Context (A : Type).
  Context `{Univalence}.

  Lemma map_union : forall X Y : FSet A, map (X ∪ Y) = max_fun (map X) (map Y).
  Proof.
    intros.
    unfold map, max_fun.
    reflexivity.
  Defined.

  Lemma k_finite_union : closedUnion (Kf_sub A).
  Proof.
    unfold closedUnion, Kf_sub, Kf_sub_intern.
    intros.
    destruct X0 as [SX XP].
    destruct X1 as [SY YP].
    exists (SX ∪ SY).
    rewrite map_union.
    rewrite XP, YP.
    reflexivity.
  Defined.

  Lemma k_finite_empty : closedEmpty (Kf_sub A).
  Proof.
    exists ∅.
    reflexivity.
  Defined.

  Lemma k_finite_singleton : closedSingleton (Kf_sub A).
  Proof.
    intro.
    exists {|a|}.
    cbn.
    apply path_forall.
    intro z.
    reflexivity.
  Defined.

  Lemma k_finite_hasDecidableEmpty : hasDecidableEmpty (Kf_sub A).
  Proof.
    unfold hasDecidableEmpty, closedEmpty, Kf_sub, Kf_sub_intern, map.
    intros.
    destruct X0 as [SX EX].
    rewrite EX.
    destruct (merely_choice SX) as [SXE | H1].
    - rewrite SXE.
      apply (tr (inl idpath)).
    - apply (tr (inr H1)).
  Defined.
End structure_k_finite.

Section k_properties.
  Context `{Univalence}.

  Lemma Kf_surjection {X Y : Type} (f : X -> Y) `{IsSurjection f} :
    Kf X -> Kf Y.
  Proof.
    intros HX. apply Kf_unfold. apply Kf_unfold in HX.
    destruct HX as [Xf HXf].
    exists (ffmap f Xf).
    intro y.
    pose (x' := center (merely (hfiber f y))).
    simple refine (@Trunc_rec (-1) (hfiber f y) _ _ _ x'). clear x'; intro x.
    destruct x as [x Hfx]. rewrite <- Hfx.
    apply fmap_isIn.
    apply (HXf x).
  Defined.

  Lemma S1_Kfinite : Kf S1.
  Proof.
    apply Kf_unfold.
    exists {|base|}.
    intro a. simpl.
    simple refine (S1_ind (fun z => Trunc (-1) (z = base)) _ _ a); simpl.
    - apply (tr loop).
    - apply path_ishprop.
  Defined.
  
  Lemma I_Kfinite : Kf interval.
  Proof.
    apply Kf_unfold.
    exists {|Interval.one|}.
    intro a. simpl.
    simple refine (interval_ind (fun z => Trunc (-1) (z = Interval.one)) _ _ _ a); simpl.
    - apply (tr seg).
    - apply (tr idpath).
    - apply path_ishprop.
  Defined.
  
End k_properties.

Section alternative_definition.
  Context `{Univalence} {A : Type}.

  Definition kf_sub (P : A -> hProp) :=
    BuildhProp(forall (K' : (A -> hProp) -> hProp),
               K' ∅ -> (forall a, K' {|a|}) -> (forall U V, K' U -> K' V -> K'(U ∪ V))
               -> K' P).

  Local Ltac help_solve :=
    repeat (let x := fresh in intro x ; destruct x) ; intros
    ; try (simple refine (path_sigma _ _ _ _ _)) ; try (apply path_ishprop) ; simpl
    ; unfold union, Sub.sub_union, max_fun
    ; apply path_forall
    ; intro z
    ; eauto with lattice_hints typeclass_instances.
  
  Definition fset_to_k : FSet A -> {P : A -> hProp & kf_sub P}.
  Proof.
    hinduction.
    - exists ∅.
      auto.
    - intros a.
      exists {|a|}.
      auto.
    - intros [P1 HP1] [P2 HP2].
      exists (P1 ∪ P2).
      intros ? ? ? HP.
      apply HP.
      * apply HP1 ; assumption.
      * apply HP2 ; assumption.
    - help_solve.
    - help_solve.
    - help_solve.
    - help_solve.
    - help_solve.
  Defined.

  Definition k_to_fset : {P : A -> hProp & kf_sub P} -> FSet A.
  Proof.
    intros [P HP].
    destruct (HP (Kf_sub _) (k_finite_empty _) (k_finite_singleton _) (k_finite_union _)).
    assumption.
  Defined.

  Lemma fset_to_k_to_fset X : k_to_fset(fset_to_k X) = X.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop) ; try (intros ; reflexivity).
    intros X1 X2 HX1 HX2.
    refine ((ap (fun z => _ ∪ z) HX2^)^ @ (ap (fun z => z ∪ X2) HX1^)^).
  Defined.
    
  Lemma k_to_fset_to_k (X : {P : A -> hProp & kf_sub P}) : fset_to_k(k_to_fset X) = X.
  Proof.
    simple refine (path_sigma _ _ _ _ _) ; try (apply path_ishprop).
    apply path_forall.
    intro z.
    destruct X as [P HP].
    unfold kf_sub in HP.
    unfold k_to_fset.
    pose (HP (Kf_sub A) (k_finite_empty A) (k_finite_singleton A) (k_finite_union A)) as t.
    assert (HP (Kf_sub A) (k_finite_empty A) (k_finite_singleton A) (k_finite_union A) = t) as X0.
    { reflexivity. }
    rewrite X0 ; clear X0.
    destruct t as [X HX].
    assert (P z = map X z) as X1.
    { rewrite HX. reflexivity. }
    simpl.
    rewrite X1 ; clear HX X1.
    hinduction X ; try (intros ; apply path_ishprop).
    - apply idpath.
    - apply (fun a => idpath). 
    - intros X1 X2 H1 H2.
      rewrite <- H1, <- H2.
      reflexivity.
  Defined.

  Theorem equiv_definition : IsEquiv fset_to_k.
  Proof.
    apply isequiv_biinv.
    split.
    - exists k_to_fset.
      intro x ; apply fset_to_k_to_fset.
    - exists k_to_fset.
      intro x ; apply k_to_fset_to_k.
  Defined.
  
End alternative_definition.