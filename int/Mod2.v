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

Instance: HitRecursion Mod2 := {
  indTy := _; recTy := _; 
  H_inductor := Mod2_ind;
  H_recursor := Mod2_rec }.

End modulo.

Definition negate : Mod2 -> Mod2.
Proof.
hrecursion.
- apply Z. 
- intros. apply (succ H).
- simpl. apply mod.
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
  + apply (Mod2_rec_beta_mod Bool false negb 1).
Defined.

Theorem adj : 
  forall x : Mod2, eq1 (Mod2_to_Bool x) = ap Mod2_to_Bool (eq2 x).
Proof.
intro x.
apply hset_bool.
Defined.

Instance: IsEquiv Mod2_to_Bool.
Proof.
apply (BuildIsEquiv Mod2 Bool Mod2_to_Bool Bool_to_Mod2 eq1 eq2 adj).
Qed.

Definition Mod2_value : Mod2 <~> Bool := BuildEquiv _ _ Mod2_to_Bool _.

Instance mod2_hset : IsHSet Mod2. 
Proof. 
apply (trunc_equiv Bool Mod2_value^-1). 
Defined.

Theorem modulo2 : forall n : Mod2, n = succ(succ n).
Proof.
hinduction.
- apply mod.
- intros n p.
  apply (ap succ p).
- apply set_path2.
Defined.

Definition plus : Mod2 -> Mod2 -> Mod2.
Proof.
intros n.
hrecursion.
- exact n.
- apply succ.
- apply modulo2.
Defined.

Lemma plus_x_Z_x : forall x, plus x Z = x.
Proof.
hinduction; cbn.
- reflexivity.
- intros n. refine (ap succ).
- apply set_path2.
Defined.

Lemma plus_S_x_S : forall x y,
 plus (succ x) y = succ (plus x y).
Proof.
intros x.
hinduction; cbn.
- reflexivity.
- intros n Hn. refine (ap succ Hn).
- apply set_path2.
Defined.

Lemma plus_x_x_Z : forall x, plus x x = Z.
Proof.
hinduction.
- reflexivity.
- intros n Hn. cbn. 
  refine (ap succ (plus_S_x_S n n) @ _).
  refine (ap (succ o succ) Hn @ _).
  apply mod^.
- apply set_path2.
Defined.

Definition mult : Mod2 -> Mod2 -> Mod2.
intros x. hrecursion.
- exact Z.
- intros y. exact (plus x y).
- simpl.
  refine (_ @ ap (plus x) (plus_x_Z_x _)^).
  apply (plus_x_x_Z x)^.
Defined.
