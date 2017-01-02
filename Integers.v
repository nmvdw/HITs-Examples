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

Module Export Ints.

Private Inductive Z : Type0 :=
| nul : Z
| succ : Z -> Z
| pred : Z -> Z.

Axiom inv1 : forall n : Z, n = pred(succ n).
Axiom inv2 : forall n : Z, n = succ(pred n).

Fixpoint Z_rec
  (P : Type)
  (a : P)
  (s : P -> P)
  (p : P -> P)
  (i1 : forall (m : P), m = p(s m))
  (i2 : forall (m : P), m = s(p m))
  (x : Z)
  {struct x}
  : P
  := 
    (match x return _ -> _ -> P with
      | nul => fun _ => fun _ => a
      | succ n => fun _ => fun _ => s ((Z_rec P a s p i1 i2) n)
      | pred n => fun _ => fun _ => p ((Z_rec P a s p i1 i2) n)
    end) i1 i2.

Axiom Z_rec_beta_inv1 : forall
  (P : Type)
  (a : P)
  (s : P -> P)
  (p : P -> P)
  (i1 : forall (m : P), m = p(s m))
  (i2 : forall (m : P), m = s(p m))
  (n : Z)
  , ap (Z_rec P a s p i1 i2) (inv1 n) = i1 (Z_rec P a s p i1 i2 n).

Axiom Z_rec_beta_inv2 : forall
  (P : Type)
  (a : P)
  (s : P -> P)
  (p : P -> P)
  (i1 : forall (m : P), m = p(s m))
  (i2 : forall (m : P), m = s(p m))
  (n : Z)
  , ap (Z_rec P a s p i1 i2) (inv2 n) = i2 (Z_rec P a s p i1 i2 n).

Fixpoint Z_ind
  (P : Z -> Type)
  (a : P nul)
  (s : forall (n : Z), P n -> P (succ n))
  (p : forall (n : Z), P n -> P (pred n))
  (i1 : forall (n : Z) (m : P n), (inv1 n) # m = p (succ n) (s (n) m))
  (i2 : forall (n : Z) (m : P n), (inv2 n) # m = s (pred n) (p (n) m))
  (x : Z)
  {struct x}
  : P x
  := 
    (match x return _ -> _ -> P x with
      | nul => fun _ => fun _ => a
      | succ n => fun _ => fun _ => s n ((Z_ind P a s p i1 i2) n)
      | pred n => fun _ => fun _ => p n ((Z_ind P a s p i1 i2) n)
    end) i1 i2.

Axiom Z_ind_beta_inv1 : forall
  (P : Z -> Type)
  (a : P nul)
  (s : forall (n : Z), P n -> P (succ n))
  (p : forall (n : Z), P n -> P (pred n))
  (i1 : forall (n : Z) (m : P n), (inv1 n) # m = p (succ n) (s (n) m))
  (i2 : forall (n : Z) (m : P n), (inv2 n) # m = s (pred n) (p (n) m))
  (n : Z)
  , apD (Z_ind P a s p i1 i2) (inv1 n) = i1 n (Z_ind P a s p i1 i2 n).

Axiom Z_ind_beta_inv2 : forall
  (P : Z -> Type)
  (a : P nul)
  (s : forall (n : Z), P n -> P (succ n))
  (p : forall (n : Z), P n -> P (pred n))
  (i1 : forall (n : Z) (m : P n), (inv1 n) # m = p (succ n) (s (n) m))
  (i2 : forall (n : Z) (m : P n), (inv2 n) # m = s (pred n) (p (n) m))
  (n : Z)
  , apD (Z_ind P a s p i1 i2) (inv2 n) = i2 n (Z_ind P a s p i1 i2 n).

End Ints.

Definition negate : Z -> Z.
Proof.
intro x.
refine (Z_rec _ _ _ _ _ _ x).
 Unshelve.
 Focus 1.
 apply nul.

 Focus 3.
 apply pred.

 Focus 3.
 apply succ.

 Focus 2.
 apply inv1.

 apply inv2.
Defined.

Definition plus : Z -> Z -> Z.
Proof.
intro x.
refine (Z_rec _ _ _ _ _ _).
 Unshelve.
 Focus 1.
 apply x.

 Focus 3.
 apply succ.

 Focus 3.
 apply pred.

 Focus 1.
 apply inv1.

 apply inv2.
Defined.

Definition minus (x : Z) (y : Z) := plus x (negate y).

Definition Z_to_S : Z -> S1.
Proof.
refine (Z_rec _ _ _ _ _ _).
  Unshelve. 

  Focus 1.
  apply base.

  Focus 3.
  intro x.
  apply x.

  Focus 3.
  intro x.
  apply x.

  Focus 1.
  intro m.
  compute.
  reflexivity.

  refine (S1_ind _ _ _).
  Unshelve.

  Focus 2.
  apply loop.

  rewrite useful.
  rewrite ap_idmap.
  rewrite concat_Vp.
  rewrite concat_1p.
  reflexivity.
Defined.

Lemma eq1 : ap Z_to_S (inv1 (pred (succ (pred nul)))) = reflexivity base.
Proof.
rewrite Z_rec_beta_inv1.
reflexivity.
Qed.


Lemma eq2 : ap Z_to_S (ap pred (inv2 (succ (pred nul)))) = loop.
Proof.
rewrite <- ap_compose.
enough (forall (n m : Z) (p : n = m), ap Z_to_S p = ap (fun n : Z => Z_to_S(pred n)) p).
  Focus 2.
  compute.
  reflexivity.

  rewrite Z_rec_beta_inv2.
  compute.
  reflexivity.
Qed.

Module Export AltInts.

Private Inductive Z' : Type0 :=
| positive : nat -> Z'
| negative : nat -> Z'.

Axiom path : positive 0 = negative 0.

Fixpoint Z'_ind
  (P : Z' -> Type)
  (po : forall (x : nat), P (positive x))
  (ne : forall (x : nat), P (negative x))
  (i : path # (po 0) = ne 0)
  (x : Z')
  {struct x}
  : P x
  := 
    (match x return _ -> P x with
      | positive n => fun _ => po n
      | negative n => fun _ => ne n
    end) i.

Axiom Z'_ind_beta_inv1 : forall
  (P : Z' -> Type)
  (po : forall (x : nat), P (positive x))
  (ne : forall (x : nat), P (negative x))
  (i : path # (po 0) = ne 0)
  , apD (Z'_ind P po ne i) path = i.
End AltInts.

Definition succ_Z' : Z' -> Z'.
Proof.
refine (Z'_ind _ _ _ _).
 Unshelve.
 Focus 2.
 intro n.
 apply (positive (S n)).

 Focus 2.
 intro n.
 induction n.
  apply (positive 1).

  apply (negative n).

 simpl.
 rewrite transport_const.
 reflexivity.
Defined.

Definition pred_Z' : Z' -> Z'.
Proof.
refine (Z'_ind _ _ _ _).
 Unshelve.
 Focus 2.
 intro n.
 induction n.
  apply (negative 1).

  apply (positive n).

 Focus 2.
 intro n.
 apply (negative (S n)).

 simpl.
 rewrite transport_const.
 reflexivity.
Defined.


Fixpoint Nat_to_Pos (n : nat) : Pos :=
  match n with
  | 0 => Int.one
  | S k => succ_pos (Nat_to_Pos k)
  end.

Definition Z'_to_Int : Z' -> Int.
Proof.
refine (Z'_ind _ _ _ _).
  Unshelve.

  Focus 2.
  intro x.
  induction x.
  apply (Int.zero).
  apply (succ_int IHx).

  Focus 2.
  intro x.
  induction x.
  apply (Int.zero).
  apply (pred_int IHx).

  simpl.
  rewrite transport_const.
  reflexivity.
Defined.

Definition Pos_to_Nat : Pos -> nat.
Proof.
intro x.
induction x.
apply 1.
apply (S IHx).
Defined.


Definition Int_to_Z' (x : Int) : Z'.
Proof.
induction x.
apply (negative (Pos_to_Nat p)).
apply (positive 0).
apply (positive (Pos_to_Nat p)).
Defined.

Lemma Z'_to_int_pos_homomorphism : 
  forall n : nat, Z'_to_Int (positive (S n)) = succ_int (Z'_to_Int (positive n)).
Proof.
intro n.
reflexivity.
Qed.

Lemma Z'_to_int_neg_homomorphism : 
  forall n : nat, Z'_to_Int (negative (S n)) = pred_int (Z'_to_Int (negative n)).
Proof.
intro n.
reflexivity.
Qed.

Theorem isoEq1 : forall x : Int, Z'_to_Int(Int_to_Z' x) = x.
Proof.
intro x.
induction x.
induction p.
reflexivity.

rewrite Z'_to_int_neg_homomorphism.
rewrite IHp.
reflexivity.

reflexivity.

induction p.
reflexivity.

rewrite Z'_to_int_pos_homomorphism.
rewrite IHp.
reflexivity.
Defined.

Lemma Int_to_Z'_succ_homomorphism :
  forall x : Int, Int_to_Z' (succ_int x) = succ_Z' (Int_to_Z' x).
Proof.
simpl.
intro x.
simpl.
induction x.
 induction p.
  compute.
  apply path.

  reflexivity.

 reflexivity.

 induction p.
  reflexivity.

  reflexivity.
Qed.

Lemma Int_to_Z'_pred_homomorphism :
  forall x : Int, Int_to_Z' (pred_int x) = pred_Z' (Int_to_Z' x).
Proof.
intro x.
induction x.
 induction p.
  reflexivity.

  reflexivity.

 reflexivity.

 induction p.
  reflexivity.

  reflexivity.

Qed.

Theorem isoEq2 : forall x : Z', Int_to_Z'(Z'_to_Int x) = x.
Proof.
refine (Z'_ind _ _ _ _).
  Unshelve.

  Focus 2.
  intro x.
  induction x.
  reflexivity.
  rewrite Z'_to_int_pos_homomorphism.
  rewrite Int_to_Z'_succ_homomorphism.
  rewrite IHx.
  reflexivity.

  Focus 2.
  intro x.
  induction x.
  apply path.
  rewrite Z'_to_int_neg_homomorphism.
  rewrite Int_to_Z'_pred_homomorphism.
  rewrite IHx.
  reflexivity.

  simpl.
  rewrite useful.
  rewrite concat_p1.
  rewrite ap_idmap.

  enough (ap (fun x : Z' => Z'_to_Int x) path = reflexivity Int.zero).
  rewrite ap_compose.
  rewrite X.
  apply concat_1p.

  apply axiomK_hset.
  apply hset_int.
Defined.

Theorem adj : 
  forall x : Z', isoEq1 (Z'_to_Int x) = ap Z'_to_Int (isoEq2 x).
Proof.
intro x.
apply hset_int.
Defined.

Definition isomorphism : IsEquiv Z'_to_Int.
Proof.
apply (BuildIsEquiv Z' Int Z'_to_Int Int_to_Z' isoEq1 isoEq2 adj).
Qed.