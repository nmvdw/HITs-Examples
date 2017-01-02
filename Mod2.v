Require Import HoTT.
Require Export HoTT.

Theorem useful :
  forall (A  B : Type)
         (f g : A -> B)
         (a a' : A)
         (p : a = a')
         (q : f a = g a),
  transport (fun x => f x = g x) p q = (ap f p)^ @ q @ (ap g p).
Proof.
intros.
induction p.
rewrite transport_1.
rewrite ap_1.
rewrite ap_1.
rewrite concat_p1.
simpl.
rewrite concat_1p.
reflexivity.
Qed.

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

Module Export moduloAlt.

Private Inductive Mod2A : Type0 :=
  | ZA : Mod2A
  | succA : Mod2A -> Mod2A.

Axiom modA : forall n : Mod2A, n = succA(succA n).

Fixpoint Mod2A_ind
  (P : Mod2A -> Type)
  (z : P ZA)
  (s : forall n : Mod2A, P n -> P (succA n))
  (mod' : forall (n : Mod2A) (a : P n),
    modA n # a = s (succA n) (s n a))
  (x : Mod2A)
  {struct x}
  : P x
  := 
    (match x return _ -> P x with
      | ZA => fun _ => z
      | succA n => fun _ => s n ((Mod2A_ind P z s mod') n)
    end) mod'.


Axiom Mod2A_ind_beta_mod : forall
  (P : Mod2A -> Type)
  (z : P ZA)
  (s : forall n : Mod2A, P n -> P (succA n))
  (mod' : forall (n : Mod2A) (a : P n),
    modA n # a = s (succA n) (s n a))
  (n : Mod2A)
  , apD (Mod2A_ind P z s mod') (modA n) = mod' n (Mod2A_ind P z s mod' n).

Fixpoint Mod2A_rec
  (P : Type)
  (z : P)
  (s : P -> P)
  (mod' : forall (a : P),
    a = s (s a))
  (x : Mod2A)
  {struct x}
  : P
  := 
    (match x return _ -> P with
      | ZA => fun _ => z
      | succA n => fun _ => s ((Mod2A_rec P z s mod') n)
    end) mod'.

Axiom Mod2A_rec_beta_mod : forall
  (P : Type)
  (z : P)
  (s : P -> P)
  (mod' : forall (a : P),
    a = s (s a))
  (n : Mod2A)
  , ap (Mod2A_rec P z s mod') (modA n) = mod' (Mod2A_rec P z s mod' n).

End moduloAlt.

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
 rewrite useful.
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
    rewrite useful.
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

Definition Mod2ToMod2A : Mod2 -> Mod2A.
Proof.
refine (Mod2_rec _ _ _ _).
 Unshelve.
 Focus 2.
 apply ZA.

 Focus 2.
 apply succA.

 Focus 1.
 simpl.
 apply modA.

Defined.

Definition Mod2AToMod2 : Mod2A -> Mod2.
Proof.
refine (Mod2A_rec _ _ _ _).
 Unshelve.
 Focus 1.
 apply Z.

 Focus 2.
 apply succ.

 Focus 1.
 intro a.
 apply (modulo2 a).
Defined.

Lemma Mod2AToMod2succA : 
 forall (n : Mod2A), Mod2AToMod2(succA n) = succ (Mod2AToMod2 n).
Proof.
reflexivity.
Defined.

Lemma Mod2ToMod2Asucc : 
 forall (n : Mod2), Mod2ToMod2A(succ n) = succA (Mod2ToMod2A n).
Proof.
reflexivity.
Defined.


Theorem eqI1 : forall (n : Mod2), n = Mod2AToMod2(Mod2ToMod2A n).
Proof.
refine (Mod2_ind _ _ _ _).
 Unshelve.
 Focus 2.
 reflexivity.

 Focus 2.
 intro n.
 intro H.
 rewrite Mod2ToMod2Asucc.
 rewrite Mod2AToMod2succA.
 rewrite <- H.
 reflexivity.

 simpl.
 rewrite useful.
 rewrite ap_idmap.
 rewrite concat_p1.
 rewrite ap_compose.
 rewrite Mod2_rec_beta_mod.
 rewrite Mod2A_rec_beta_mod.
  simpl.
  simpl.
  enough (modulo2 Z = mod).
   rewrite X.
   apply concat_Vp.

   compute.
   reflexivity.

Defined.

Theorem eqI2 : forall (n : Mod2A), n = Mod2ToMod2A(Mod2AToMod2 n).
Proof.
refine (Mod2A_ind _ _ _ _).
 Focus 1.
 reflexivity.

 Unshelve.
  Focus 2.
  intros.
  rewrite Mod2AToMod2succA.
  rewrite Mod2ToMod2Asucc.
  rewrite <- X.
  reflexivity.

  intros.
  simpl.
  rewrite useful.
  rewrite ap_idmap.
  rewrite ap_compose.
  rewrite Mod2A_rec_beta_mod.