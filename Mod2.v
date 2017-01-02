Require Import HoTT.
Require Export HoTT.

Module Export modulo.

Private Inductive Mod2 : Type0 :=
  | Z : Mod2
  | succ : Mod2 -> Mod2.

Axiom mod : Z = succ(succ Z).

Fixpoint Mod2_ind
  (P : Mod2 -> Type)
  (a : P Z)
  (s : forall (n : Mod2), P n -> P (succ n))
  (mod' : mod # a = s (succ Z) (s Z a))
  (x : Mod2)
  {struct x}
  : P x
  := 
    (match x return _ -> P x with
      | Z => fun _ => a
      | succ n => fun _ => s n ((Mod2_ind P a s mod') n)
    end) mod'.

Axiom Mod2_ind_beta_mod : forall
  (P : Mod2 -> Type)
  (a : P Z)
  (s : forall (n : Mod2), P n -> P (succ n))
  (mod' : mod # a = s (succ Z) (s Z a))
  , apD (Mod2_ind P a s mod') mod = mod'.

Fixpoint Mod2_rec
  (P : Type)
  (a : P)
  (s : P -> P)
  (mod' : a = s (s a))
  (x : Mod2)
  {struct x}
  : P
  := 
    (match x return _ -> P with
      | Z => fun _ => a
      | succ n => fun _ => s ((Mod2_rec P a s mod') n)
    end) mod'.

Axiom Mod2_rec_beta_mod : forall
  (P : Type)
  (a : P)
  (s : P -> P)
  (mod' : a = s (s a))
  , ap (Mod2_rec P a s mod') mod = mod'.

End modulo.

Definition negate : Mod2 -> Mod2.
Proof.
refine (Mod2_ind _ _ _ _).
 Unshelve.
 Focus 2.
 apply (succ Z).

 Focus 2.
 intros.
 apply (succ H).

 simpl.
 rewrite transport_const.
 rewrite <- mod.
 reflexivity.
Defined.

Theorem modulo2 : forall n : Mod2, n = succ(succ n).
Proof.
refine (Mod2_ind _ _ _ _).
 Unshelve.
 Focus 2.
 apply mod.

 Focus 2.
 intro n.
 intro p.
 apply (ap succ p).

 simpl.
 rewrite @HoTT.Types.Paths.transport_paths_FlFr.
 rewrite ap_idmap.
 rewrite concat_Vp.
 rewrite concat_1p.
 rewrite ap_compose.
 reflexivity.
Defined.

Definition plus : Mod2 -> Mod2 -> Mod2.
Proof.
intro n.
refine (Mod2_ind _ _ _ _).
  Unshelve.

  Focus 2.
  apply n.

  Focus 2.
  intro m.
  intro k.
  apply (succ k).

  simpl.
  rewrite transport_const.
  apply modulo2.
Defined.

Definition Bool_to_Mod2 : Bool -> Mod2.
Proof.
intro b.
destruct b.
 apply (succ Z).

 apply Z.
Defined.

Definition Mod2_to_Bool : Mod2 -> Bool.
Proof.
refine (Mod2_ind _ _ _ _).
 Unshelve.
 Focus 2.
 apply false.

 Focus 2.
 intro n.
 apply negb.

 Focus 1.
 simpl.
 apply transport_const.
Defined.

Theorem eq1 : forall n : Bool, Mod2_to_Bool (Bool_to_Mod2 n) = n.
Proof.
intro b.
destruct b.
 Focus 1.
 compute.
 reflexivity.

 compute.
 reflexivity.
Qed.

Theorem Bool_to_Mod2_negb : forall x : Bool, 
  succ (Bool_to_Mod2 x) = Bool_to_Mod2 (negb x).
Proof.
intros.
destruct x.
 compute.
 apply mod^.

 compute.
 apply reflexivity.
Defined.

Theorem eq2 : forall n : Mod2, Bool_to_Mod2 (Mod2_to_Bool n) = n.
Proof.
refine (Mod2_ind _ _ _ _).
  Unshelve.
  Focus 2.
  compute.
  reflexivity.

  Focus 2.
  intro n.
  intro IHn.
  symmetry.
  transitivity (succ (Bool_to_Mod2 (Mod2_to_Bool n))).

    Focus 1.
    symmetry.
    apply (ap succ IHn).

    transitivity (Bool_to_Mod2 (negb (Mod2_to_Bool n))).
    apply Bool_to_Mod2_negb.
    enough (negb (Mod2_to_Bool n) = Mod2_to_Bool (succ n)).
    apply (ap Bool_to_Mod2 X).

    compute.
    reflexivity.
    simpl.
    rewrite concat_p1.
    rewrite concat_1p.
    rewrite @HoTT.Types.Paths.transport_paths_FlFr.
    rewrite concat_p1.
    rewrite ap_idmap.
    rewrite ap_compose.

    enough (ap Mod2_to_Bool mod = reflexivity false).
    rewrite X.
    simpl.
    rewrite concat_1p.
    rewrite inv_V.
    reflexivity.

    enough (IsHSet Bool).
    apply axiomK_hset.
    apply X.
    apply hset_bool.
Defined.

Theorem adj : 
  forall x : Mod2, eq1 (Mod2_to_Bool x) = ap Mod2_to_Bool (eq2 x).
Proof.
intro x.
enough (IsHSet Bool).
apply set_path2.
apply hset_bool.
Defined.

Definition isomorphism : IsEquiv Mod2_to_Bool.
Proof.
apply (BuildIsEquiv Mod2 Bool Mod2_to_Bool Bool_to_Mod2 eq1 eq2 adj).
Qed.