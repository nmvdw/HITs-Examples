Require Import HoTT.
Require Export HoTT.

Module Export FinSet.

Private Inductive FinSets (A : Type) : Type :=
  | empty : FinSets A
  | L : A -> FinSets A
  | U : FinSets A -> FinSets A -> FinSets A.

Axiom assoc : forall (A : Type) (x y z : FinSets A),
  U A x (U A y z) = U A (U A x y) z.

Axiom comm : forall (A : Type) (x y : FinSets A),
  U A x y = U A y x.

Axiom nl : forall (A : Type) (x : FinSets A),
  U A (empty A) x = x.

Axiom nr : forall (A : Type) (x : FinSets A),
  U A x (empty A) = x.

Axiom idem : forall (A : Type) (x : A),
  U A (L A x) (L A x) = L A x.

Fixpoint FinSets_rec
  (A : Type)
  (P : Type)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : FinSets A)
  {struct x}
  : P
  := (match x return _ -> _ -> _ -> _ -> _ -> P with
        | empty => fun _ => fun _ => fun _ => fun _ => fun _ => e
        | L a => fun _ => fun _ => fun _ => fun _ => fun _ => l a
        | U y z => fun _ => fun _ => fun _ => fun _ => fun _ => u 
           (FinSets_rec A P e l u assocP commP nlP nrP idemP y)
           (FinSets_rec A P e l u assocP commP nlP nrP idemP z)
      end) assocP commP nlP nrP idemP.

Axiom FinSets_beta_assoc : forall
  (A : Type)
  (P : Type)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x y z : FinSets A),
  ap (FinSets_rec A P e l u assocP commP nlP nrP idemP) (assoc A x y z)
  =
  (assocP (FinSets_rec A P e l u assocP commP nlP nrP idemP x)
          (FinSets_rec A P e l u assocP commP nlP nrP idemP y)
          (FinSets_rec A P e l u assocP commP nlP nrP idemP z)
  ).

Axiom FinSets_beta_comm : forall
  (A : Type)
  (P : Type)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x y : FinSets A),
  ap (FinSets_rec A P e l u assocP commP nlP nrP idemP) (comm A x y)
  =
  (commP (FinSets_rec A P e l u assocP commP nlP nrP idemP x)
         (FinSets_rec A P e l u assocP commP nlP nrP idemP y)
  ).

Axiom FinSets_beta_nl : forall
  (A : Type)
  (P : Type)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : FinSets A),
  ap (FinSets_rec A P e l u assocP commP nlP nrP idemP) (nl A x)
  =
  (nlP (FinSets_rec A P e l u assocP commP nlP nrP idemP x)
  ).

Axiom FinSets_beta_nr : forall
  (A : Type)
  (P : Type)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : FinSets A),
  ap (FinSets_rec A P e l u assocP commP nlP nrP idemP) (nr A x)
  =
  (nrP (FinSets_rec A P e l u assocP commP nlP nrP idemP x)
  ).

Axiom FinSets_beta_idem : forall
  (A : Type)
  (P : Type)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : A),
  ap (FinSets_rec A P e l u assocP commP nlP nrP idemP) (idem A x)
  =
  idemP x.
End FinSet.

Definition isIn : forall 
  (A : Type)
  (eq : A -> A -> Bool),
  A -> FinSets A -> Bool.
Proof.
intro A.
intro eq.
intro a.
refine (FinSets_rec A _ _ _ _ _ _ _ _ _).
  Unshelve.

  Focus 6.
  apply false.

  Focus 6.
  intro a'.
  apply (eq a a').

  Focus 6.
  intro b.
  intro b'.
  apply (orb b b').

  Focus 3.
  intros.
  compute.
  reflexivity.

  Focus 1.
  intros.
  compute.
  destruct x.
  reflexivity.
  destruct y.
  reflexivity.
  reflexivity.

  Focus 1.
  intros.
  compute.
  destruct x.
  destruct y.
  reflexivity.
  reflexivity.
  destruct y.
  reflexivity.
  reflexivity.

  Focus 1.
  intros.
  compute.
  destruct x.
  reflexivity.
  reflexivity.

  intros.
  compute.
  destruct (eq a x).
  reflexivity.
  reflexivity.
Defined.

Definition comprehension : forall
  (A : Type)
  (eq : A -> A -> Bool),
  (A -> Bool) -> FinSets A -> FinSets A.
Proof.
intro A.
intro eq.
intro phi.
refine (FinSets_rec A _ _ _ _ _ _ _ _ _).
  Unshelve.

  Focus 6.
  apply empty.

  Focus 6.
  intro a.
  apply (if (phi a) then L A a else (empty A)).

  Focus 6.
  intro x.
  intro y.
  apply (U A x y).

  Focus 3.
  intros.
  compute.
  apply nl.

  Focus 1.
  intros.
  compute.
  apply assoc.

  Focus 1.
  intros.
  compute.
  apply comm.

  Focus 1.
  intros.
  compute.
  apply nr.

  intros.
  compute.
  destruct (phi x).
  apply idem.
  apply nl.
Defined.

Definition intersection : forall (A : Type) (eq : A -> A -> Bool), 
  FinSets A -> FinSets A -> FinSets A.
Proof.
intro A.
intro eq.
intro x.
intro y.
apply (comprehension A eq (fun (a : A) => isIn A eq a x) y).
Defined.

Definition subset (A : Type) (eq : A -> A -> Bool) (x : FinSets A) (y : FinSets A) : Bool.
Proof.
refine (FinSets_rec A _ _ _ _ _ _ _ _ _ _).
  Unshelve.

  Focus 6.
  apply x.

  Focus 6.
  apply true.

  Focus 6.
  intro a.
  apply (isIn A eq a y).

  Focus 6.
  intro b.
  intro b'.
  apply (andb b b').

  Focus 1.
  intros.
  compute.
  destruct x0.
  destruct y0.
  reflexivity.
  reflexivity.
  reflexivity.

  Focus 1.
  intros.
  compute.
  destruct x0.
  destruct y0.
  reflexivity.
  reflexivity.
  destruct y0.
  reflexivity.
  reflexivity.

  Focus 1.
  intros.
  compute.
  reflexivity.

  Focus 1.
  intros.
  compute.
  destruct x0.
  reflexivity.
  reflexivity.

  intros.
  destruct (isIn A eq x0 y).
  compute.
  reflexivity.
  compute.
  reflexivity.
Defined.

Definition equal_set (A : Type) (eq : A -> A -> Bool) (x : FinSets A) (y : FinSets A) : Bool
  := andb (subset A eq x y) (subset A eq y x).

Fixpoint eq_nat n m : Bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat n1 m1
  end.