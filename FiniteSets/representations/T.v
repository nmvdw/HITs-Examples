(* Type which proves that all types have merely decidable equality implies LEM *)
Require Import HoTT HitTactics Sub.

Section TR.
  Context `{Univalence}.
  Variable A : hProp.

  Definition T := Unit + Unit.

  Definition R (x y : T) : hProp :=
    match x, y with
    | inl tt, inl tt => Unit_hp
    | inl tt, inr tt => A
    | inr tt, inl tt => A
    | inr tt, inr tt => Unit_hp
    end.

  Global Instance R_mere : is_mere_relation _ R.
  Proof.
    intros x y ; destruct x ; destruct y ; apply _.
  Defined.

  Global Instance R_refl : Reflexive R.
  Proof.
    intro x ; destruct x as [[ ] | [ ]] ; apply tt.
  Defined.
  
  Global Instance R_sym : Symmetric R.
  Proof.
    repeat (let x := fresh in intro x ; destruct x as [[ ] | [ ]])
    ; auto ; apply tt.
  Defined.
  
  Global Instance R_trans : Transitive R.
  Proof.
    repeat (let x := fresh in intro x ; destruct x as [[ ] | [ ]]) ; intros
    ; auto ; apply tt.
  Defined.

  Definition TR : Type := quotient R.
  Definition TR_zero : TR := class_of R (inl tt).
  Definition TR_one : TR := class_of R (inr tt).

  Definition equiv_pathspace_T : (TR_zero = TR_one) = (R (inl tt) (inr tt))
    := path_universe (sets_exact R (inl tt) (inr tt)).

  Global Instance quotientB_recursion : HitRecursion TR :=
    {
      indTy := _;
      recTy :=
        forall (P : Type) (HP: IsHSet P) (u : T -> P),
          (forall x y : T, R x y -> u x = u y) -> TR -> P;
      H_inductor := quotient_ind R ;
      H_recursor := @quotient_rec _ R _
    }.

End TR.

Theorem merely_dec `{Univalence} : (forall (A : Type) (a b : A), hor (a = b) (~a = b))
                                   ->
                                   forall (A : hProp), A + (~A).
Proof.
  intros X A.
  specialize (X (TR A) (TR_zero A) (TR_one A)).
  rewrite equiv_pathspace_T in X.
  strip_truncations.
  apply X.
Defined.