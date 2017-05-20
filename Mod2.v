Require Export HoTT.

Require Import HitTactics.
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


Definition Mod2CL : HitRec.class Mod2 _ _ := 
   HitRec.Class Mod2 (fun x P a s p => Mod2_rec P a s p x) (fun x P a s p => Mod2_ind P a s p x).
Canonical Structure Mod2ty : HitRec.type := HitRec.Pack Mod2 _ _ Mod2CL.

End modulo.


Theorem modulo2 : forall n : Mod2, n = succ(succ n).
Proof.
intro n.
hrecursion n.
- apply mod.
- intros n p.
  apply (ap succ p).
- simpl.
  etransitivity.
  eapply (@transport_paths_FlFr _ _ idmap (fun n => succ (succ n))).
  hott_simpl.
  apply ap_compose.
Defined.

Definition negate : Mod2 -> Mod2.
Proof.
intro x.
hrecursion x.
- apply Z. 
- intros. apply (succ H).
- simpl. apply mod.
Defined.

Definition plus : Mod2 -> Mod2 -> Mod2.
Proof.
intros n m.
hrecursion m.
- exact n.
- apply succ.
- apply modulo2.
Defined.

Definition Bool_to_Mod2 : Bool -> Mod2.
Proof.
intro b.
destruct b.
+ apply (succ Z).
+ apply Z.
Defined.

Definition Mod2_to_Bool : Mod2 -> Bool.
Proof.
intro x.
hrecursion x.
- exact false.
- exact negb.
- simpl. reflexivity.
Defined.

Theorem eq1 : forall n : Bool, Mod2_to_Bool (Bool_to_Mod2 n) = n.
Proof.
intro b.
destruct b; compute; reflexivity.
Qed.

Theorem Bool_to_Mod2_negb : forall x : Bool, 
  succ (Bool_to_Mod2 x) = Bool_to_Mod2 (negb x).
Proof.
intros.
destruct x; compute.
+ apply mod^.
+ apply reflexivity.
Defined.

Theorem eq2 : forall n : Mod2, Bool_to_Mod2 (Mod2_to_Bool n) = n.
Proof.
intro n.
hinduction n.
- reflexivity.
- intros n IHn.
  symmetry. etransitivity. apply (ap succ IHn^). 
  etransitivity. apply Bool_to_Mod2_negb.
  hott_simpl.
- rewrite @HoTT.Types.Paths.transport_paths_FlFr.
  hott_simpl.
  rewrite ap_compose. 
  enough (ap Mod2_to_Bool mod = idpath).
  + rewrite X. hott_simpl.
  + unfold Mod2_to_Bool. unfold HitRec.hrecursion. simpl. 
    apply (Mod2_rec_beta_mod Bool false negb 1).
Defined.

Theorem adj : 
  forall x : Mod2, eq1 (Mod2_to_Bool x) = ap Mod2_to_Bool (eq2 x).
Proof.
intro x.
apply hset_bool.
Defined.

Definition isomorphism : IsEquiv Mod2_to_Bool.
Proof.
apply (BuildIsEquiv Mod2 Bool Mod2_to_Bool Bool_to_Mod2 eq1 eq2 adj).
Qed.