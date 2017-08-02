Require Import HoTT HitTactics.
Require Import lattice representations.definition fsets.operations extensionality.

Definition Sub A := A -> hProp.

Section k_finite.

  Context {A : Type}.
  Context `{Univalence}.

  Instance subA_set : IsHSet (Sub A).
  Proof.
    apply _.
  Defined.

  Definition map (X : FSet A) : Sub A := fun a => isIn a X.

  Instance map_injective : IsEmbedding map.
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

  Lemma Kf_unfold : Kf <-> (exists (X : FSet A), forall (a : A), map X a).
  Proof.
    split.
    - intros [X PX]. exists X. intro a.
      rewrite <- PX. done.
    - intros [X PX]. exists X. apply path_forall; intro a.
      apply path_hprop.
      symmetry. apply if_hprop_then_equiv_Unit; [ apply _ | ].
      apply PX.
  Defined.

End k_finite.
