Require Import HoTT.

(* Lemmas from this file do not belong in this project. *)
(* Some of them should probably be in the HoTT library? *)

Lemma ap_inl_path_sum_inl {A B} (x y : A) (p : inl x = inl y) :
  ap inl (path_sum_inl B p) = p.
Proof.
  transitivity (@path_sum _ B (inl x) (inl y) (path_sum_inl B p));
    [ | apply (eisretr_path_sum _) ].
  destruct (path_sum_inl B p).
  reflexivity.
Defined.
Lemma ap_equiv {A B} (f : A <~> B) {x y : A} (p : x = y) :
  ap (f^-1 o f) p = eissect f x @ p @ (eissect f y)^.
Proof. destruct p. hott_simpl. Defined.

Global Instance hprop_lem `{Univalence} (T : Type) (Ttrunc : IsHProp T) : IsHProp (T + ~T).
  Proof.
    apply (equiv_hprop_allpath _)^-1.
    intros [x | nx] [y | ny] ; try f_ap ; try (apply Ttrunc) ; try contradiction.
    - apply equiv_hprop_allpath. apply _.
  Defined.
