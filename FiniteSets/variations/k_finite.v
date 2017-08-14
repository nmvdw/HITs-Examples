Require Import HoTT HitTactics.
Require Import lattice representations.definition fsets.operations extensionality Sub fsets.properties.

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
