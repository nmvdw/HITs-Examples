Require Import HoTT.

Local Open Scope nat_scope.

(*
  Expressions with natural numbers and +.
*)
Section plus.

Private Inductive ExpP : Type :=
| val : nat -> ExpP
| plus : ExpP -> ExpP -> ExpP.

Axiom addE : forall n m, plus (val n) (val m) = val (n + m).

Fixpoint ExpP_ind
  (Y : ExpP -> Type)
  (vY : forall n : nat, Y(val n))
  (pY : forall e1 e2 : ExpP, Y e1 -> Y e2 -> Y (plus e1 e2))
  (aY : forall n m : nat, addE n m # pY (val n) (val m) (vY n) (vY m) = vY (n + m))
  (x : ExpP)
  {struct x}
  : Y x
  :=
  (match x return _ -> Y x with
    | val n => fun _ => vY n
    | plus e1 e2 => fun _ => pY e1 e2 (ExpP_ind Y vY pY aY e1) (ExpP_ind Y vY pY aY e2)
  end) aY.

Axiom ExpP_ind_beta_addE : forall
  (Y : ExpP -> Type)
  (vY : forall n : nat, Y(val n))
  (pY : forall e1 e2 : ExpP, Y e1 -> Y e2 -> Y (plus e1 e2))
  (aY : forall n m : nat, addE n m # pY (val n) (val m) (vY n) (vY m) = vY (n + m))
  (n m : nat)
  , apD (ExpP_ind Y vY pY aY) (addE n m) = aY n m.

End plus.

(*
  Evaluates the expression, truncation is needed for images of the path.
*)
Definition evalExp : forall (e : ExpP), exists n : nat, 
  Trunc (trunc_S minus_two) (e = val n).
Proof.
Proof.
simple refine (ExpP_ind _ _ _ _); cbn.
- intros.
  exists n.
  apply tr.
  reflexivity.
- intros e1 e2 (v1, tp1) (v2, tp2).
  exists (v1 + v2).
  (* alternative option:
        simple refine (_ @ addE v1 v2).
        simple refine (_ @ ap (plus (val v1)) p2).
        apply (ap (fun x => plus x e2) p1).
  *)
  simple refine (Trunc_ind _ _ tp1).
  intro p1.
  simple refine (Trunc_ind _ _ tp2).
  intro p2.
  cbn.
  apply tr.
  apply (
    ap (plus e1) p2
    @ ap (fun x => plus x (val v2)) p1
    @ addE v1 v2).
- intros.
  simple refine (path_sigma _ _ _ _ _).
  * cbn.
    simple refine
      (ap pr1 (@transport_sigma ExpP _ _ _ _ (addE n m) (n + m; tr (1 @ addE n m))) @ _).
    simple refine 
      (transport_const (addE n m) _ @ _).
    reflexivity.
  * enough
      (forall (e1 e2 : ExpP) (x1 x2 : Trunc (trunc_S minus_two) (e1 = e2)),
        x1 = x2).
    apply X.
    intros.
    enough (IsHProp (Trunc -1 (e1 = e2))).
      apply X.
      apply istrunc_truncation.
Defined.

(*
  Value of an expression
*)
Definition value (e : ExpP) := pr1 (evalExp e).

(*
  For tests, sum from 0 to n
*)
Fixpoint gauss (n : nat) :=
match n with
  | 0 => val 0
  | S n => plus (val (S n)) (gauss n)
end.

(*
  Denotational semantics of expressions as natural numbers
*)
Definition denotationalN : ExpP -> nat.
Proof.
simple refine (ExpP_ind _ _ _ _); cbn.
- apply idmap.
- intros e1 e2 n m.
  apply (n + m).
- intros.
  apply transport_const.
Defined.

(*
  Denotational semantics of expressions as loops on circle
*)
Definition denotationalS1 : ExpP -> base = base.
Proof.
simple refine (ExpP_ind _ _ _ _); cbn.
- induction 1.
  * reflexivity.
  * apply (loop @ IHn).
- intros e1 e2 p1 p2.
  apply (p1 @ p2).
- intros n m.
  simple refine (transport_paths_FlFr _ _ @ _).
  hott_simpl.
  cbn.
  induction n ; induction m ; cbn.
  * reflexivity.
  * apply concat_1p.
  * etransitivity.
    apply concat_p1.
    cbn in IHn.
    simple refine (ap (fun p => loop @ p) _).
    etransitivity.
      Focus 2.
      apply IHn.

      symmetry.
      apply concat_p1.
  * etransitivity.
    apply concat_pp_p.
    simple refine (ap (fun p => loop @ p) _).
    induction n.
      apply concat_1p.
      cbn in *.
      apply IHn.
Defined.

Definition power {A : Type} {x : A} (p : x = x) (n : nat) : x = x.
Proof.
induction n.
- reflexivity.
- apply (p @ IHn).
Defined.

Lemma power_plus : forall (A : Type) (x : A) (p : x = x) n m, 
  power p (n + m) = (power p n) @ (power p m).
Proof.
induction n; simpl.
- induction m; cbn; hott_simpl.
- induction m; simpl.
  * rewrite <- nat_plus_n_O.
    hott_simpl.
  * rewrite IHn.
    hott_simpl.
Defined.

Theorem sem : forall (e : ExpP), 
  Trunc (trunc_S minus_two) (denotationalS1 e = power loop (denotationalN e)).
Proof.
simple refine (ExpP_ind _ _ _ _); simpl.
- intros.
  apply tr.
  reflexivity.
- intros e1 e2 tp1 tp2.
  simple refine (Trunc_ind _ _ tp1).
  intro p1.
  simple refine (Trunc_ind _ _ tp2).
  intro p2.
  simpl.
  apply tr.
  assert
    (power loop (denotationalN (plus e1 e2)) =
     power loop (denotationalN e1 + denotationalN e2)).
    { reflexivity. }
  rewrite X.
  cbn.
  rewrite p1; rewrite p2.
  rewrite power_plus.
  reflexivity.
- intros.
  enough
    (forall (e1 e2 : base = base) (x1 x2 : Trunc (trunc_S minus_two) (e1 = e2)),
    x1 = x2).
  apply X.

  intros.
  enough (IsHProp (Trunc -1 (e1 = e2))).
    apply X.

    apply istrunc_truncation.
Defined.