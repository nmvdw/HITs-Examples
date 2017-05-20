Require Export HoTT.
Require Import HitTactics.

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

(* TODO: add an induction principle *)
Definition FinSetsCL A : HitRec.class (FinSets A) _ _ := 
   HitRec.Class (FinSets A) (fun x P e l u aP cP lP rP iP => FinSets_rec A P e l u aP cP lP rP iP x) (fun x P e l u aP cP lP rP iP => FinSets_rec A P e l u aP cP lP rP iP x).
Canonical Structure FinSetsTy A : HitRec.type := HitRec.Pack _ _ _ (FinSetsCL A).

End FinSet.

Section functions.
Parameter A : Type.
Parameter eq : A -> A -> Bool.
Definition isIn : A -> FinSets A -> Bool.
Proof.
intros a X.
hrecursion X.
- exact false.
- intro a'. apply (eq a a').
- apply orb. 
- intros x y z. compute. destruct x; reflexivity.
- intros x y. compute. destruct x, y; reflexivity.
- intros x. compute. reflexivity. 
- intros x. compute. destruct x; reflexivity.
- intros a'. compute. destruct (eq a a'); reflexivity.
Defined.


Definition comprehension : 
  (A -> Bool) -> FinSets A -> FinSets A.
Proof.
intros P X.
hrecursion X.
- apply empty.
- intro a.
  refine (if (P a) then L A a else empty A).
- intros X Y.
  apply (U A X Y).
- intros. cbv. apply assoc.
- intros. cbv. apply comm.
- intros. cbv. apply nl.
- intros. cbv. apply nr.
- intros. cbv. 
  destruct (P x); simpl.
  + apply idem.
  + apply nl.
Defined.

Definition intersection : 
  FinSets A -> FinSets A -> FinSets A.
Proof.
intros X Y.
apply (comprehension (fun (a : A) => isIn a X) Y).
Defined.

Definition subset (x : FinSets A) (y : FinSets A) : Bool.
Proof.
hrecursion x.
- apply true.
- intro a. apply (isIn a y).
- apply andb.
- intros a b c. compute. destruct a; reflexivity.
- intros a b. compute. destruct a, b; reflexivity.
- intros x. compute. reflexivity.
- intros x. compute. destruct x;reflexivity.
- intros a. simpl. 
  destruct (isIn a y); reflexivity.
Defined.

Definition subset' (x : FinSets A) (y : FinSets A) : Bool.
Proof.
refine (FinSets_rec A _ _ _ _ _ _ _ _ _ _).
  Unshelve.

  Focus 6.
  apply x.

  Focus 6.
  apply true.

  Focus 6.
  intro a.
  apply (isIn a y).

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
  destruct (isIn x0 y).
  compute.
  reflexivity.
  compute.
  reflexivity.
Defined.
(* TODO: subset = subset' *)

Definition equal_set (x : FinSets A) (y : FinSets A) : Bool
  := andb (subset x y) (subset y x).

Fixpoint eq_nat n m : Bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat n1 m1
  end.

End functions.