Require Import FSets list_representation.
Require Import kuratowski.length misc.dec_kuratowski.
From FSets.interfaces Require Import lattice_interface.
From FSets.subobjects Require Import sub b_finite enumerated k_finite.

Require Import HoTT.Spaces.Card.

Section contents.
  Context `{Univalence}.
  
  Definition isKf_card (X : Card) : hProp.
  Proof.
    strip_truncations.
    refine (Kf X).
  Defined.

  Definition Kf_card := BuildhSet (@sig Card isKf_card).

  Definition Kf_card' := BuildhSet (Trunc 0 (@sig hSet (fun X => Kf X))).

  Definition f : Kf_card -> Kf_card'.
  Proof.
    intros [X HX].
    unfold Kf_card'.
    revert HX. strip_truncations.
    intros HX.
    apply tr.
    exists X.
    apply HX.
  Defined.

  Definition g : Kf_card' -> Kf_card.
  Proof.
    unfold Kf_card, Kf_card'.
    intros X. strip_truncations.
    destruct X as [X HX].
    exists (tr X). apply HX.
  Defined.

  Instance f_equiv : IsEquiv f.
  Proof.
    apply isequiv_biinv.
    split; exists g.
    - unfold Sect. unfold Kf_card. simpl.
      intros [X HX].
      revert HX. strip_truncations. intros HX.
      simpl. reflexivity.
    - intros X. strip_truncations. simpl.
      reflexivity.
  Defined.

  Lemma kf_card_equiv :
    Kf_card = Kf_card'.
  Proof.
    apply path_hset.
    simple refine (BuildEquiv Kf_card Kf_card' f _).
  Defined.

End contents.
