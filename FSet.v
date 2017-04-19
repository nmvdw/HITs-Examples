Require Import HoTT.
Require Export HoTT.

Module Export FinSet.

Set Implicit Arguments.

Parameter A: Type.

Private Inductive FSet : Type :=
  | empty : FSet 
  | L : A -> FSet 
  | U : FSet -> FSet -> FSet.
Infix  "∪" := U (at level 8, right associativity).
Notation "∅" := empty.


Axiom assoc : forall (x y z : FSet),
 x ∪ (y ∪ z)  = (x ∪ y) ∪ z. 

Axiom comm : forall (x y : FSet),
 x ∪ y = y ∪ x.

Axiom neutl : forall  (x : FSet),
 ∅ ∪ x = x.

Axiom neutr : forall (x : FSet),
 x ∪  ∅  = x.

Axiom idem : forall (x : A),
  (L x) ∪ (L x) = L x.

Axiom trunc : IsHSet FSet.

Fixpoint FSet_rec
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : FSet)
  {struct x}
  : P
  := (match x return _ -> _ -> _ -> _ -> _ -> _ -> P with
        | empty => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => e
        | L a => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => l a
        | U y z => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => u 
           (FSet_rec H e l u assocP commP nlP nrP idemP y)
           (FSet_rec H e l u assocP commP nlP nrP idemP z)
      end) assocP commP nlP nrP idemP H.


Axiom FSet_rec_beta_assoc : forall
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x y z : FSet),
  ap (FSet_rec H e l u assocP commP nlP nrP idemP) (assoc x y z) 
  =
  (assocP (FSet_rec H e l u assocP commP nlP nrP idemP x)
          (FSet_rec H e l u assocP commP nlP nrP idemP y)
          (FSet_rec H e l u assocP commP nlP nrP idemP z)
  ).

Axiom FSet_rec_beta_comm : forall
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x y : FSet),
  ap (FSet_rec H e l u assocP commP nlP nrP idemP) (comm x y)
  =
  (commP (FSet_rec H e l u assocP commP nlP nrP idemP x)
         (FSet_rec H e l u assocP commP nlP nrP idemP y)
  ).

Axiom FSet_rec_beta_nl : forall
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : FSet),
  ap (FSet_rec H e l u assocP commP nlP nrP idemP) (neutl x)
  =
  (nlP (FSet_rec H e l u assocP commP nlP nrP idemP x)
  ).

Axiom FSet_rec_beta_nr : forall
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : FSet),
  ap (FSet_rec H e l u assocP commP nlP nrP idemP) (neutr x)
  =
  (nrP (FSet_rec H e l u assocP commP nlP nrP idemP x)
  ).

Axiom FSet_rec_beta_idem : forall
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : A),
  ap (FSet_rec H e l u assocP commP nlP nrP idemP) (idem x)
  =
  idemP x.

Fixpoint FSet_ind
  (P : FSet -> Type)
  (H :  forall a : FSet, IsHSet (P a))
  (eP : P empty)
  (lP : forall a: A, P (L a))
  (uP : forall (x y: FSet), P x -> P y -> P (U x y))
  (assocP : forall (x y z : FSet) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz))
  (commP : forall (x y: FSet) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px) 
  (nlP : forall (x : FSet) (px: P x), 
  neutl x # uP empty x eP px = px)
  (nrP : forall (x : FSet) (px: P x), 
  neutr x # uP x empty px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x : FSet)
  {struct x}
  : P x
  := (match x return _ -> _ -> _ -> _ -> _ -> _ -> P x with
        | empty => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => eP
        | L a => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => lP a
        | U y z => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => uP y z
           (FSet_ind P H eP lP uP assocP commP nlP nrP idemP y)
           (FSet_ind P H eP lP uP assocP commP nlP nrP idemP z)
      end) H assocP commP nlP nrP idemP.


Axiom FSet_ind_beta_assoc : forall
  (A : Type)
  (P : FSet A -> Type)
  (eP : P (empty A))
  (lP : forall a: A, P (L a))
  (uP : forall (x y: FSet A), P x -> P y -> P (U x y))
  (assocP : forall (x y z : FSet A) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz))
  (commP : forall (x y: FSet A) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px) 
  (nlP : forall (x : FSet A) (px: P x), 
  nl x # uP (empty A) x eP px = px)
  (nrP : forall (x : FSet A) (px: P x), 
  nr x # uP x (empty A) px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x y z : FSet A),
  apD (FSet_ind P eP lP uP assocP commP nlP nrP idemP) 
      (assoc x y z)
  =
  (assocP x y z 
          (FSet_ind P eP lP uP assocP commP nlP nrP idemP x)
          (FSet_ind P eP lP uP assocP commP nlP nrP idemP y)
          (FSet_ind P eP lP uP assocP commP nlP nrP idemP z)
  ).



Axiom FSet_ind_beta_comm : forall
  (A : Type)
  (P : FSet A -> Type)
  (eP : P (empty A))
  (lP : forall a: A, P (L a))
  (uP : forall (x y: FSet A), P x -> P y -> P (U x y))
  (assocP : forall (x y z : FSet A) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz))
  (commP : forall (x y: FSet A) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px) 
  (nlP : forall (x : FSet A) (px: P x), 
  nl x # uP (empty A) x eP px = px)
  (nrP : forall (x : FSet A) (px: P x), 
  nr x # uP x (empty A) px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x y : FSet A),
  apD (FSet_ind P eP lP uP assocP commP nlP nrP idemP) (comm x y)
  =
  (commP x y 
         (FSet_ind P eP lP uP assocP commP nlP nrP idemP x)
         (FSet_ind P eP lP uP assocP commP nlP nrP idemP y)
  ).

Axiom FSet_ind_beta_nl : forall
  (A : Type)
  (P : FSet A -> Type)
  (eP : P (empty A))
  (lP : forall a: A, P (L a))
  (uP : forall (x y: FSet A), P x -> P y -> P (U x y))
  (assocP : forall (x y z : FSet A) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz))
  (commP : forall (x y: FSet A) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px) 
  (nlP : forall (x : FSet A) (px: P x), 
  nl x # uP (empty A) x eP px = px)
  (nrP : forall (x : FSet A) (px: P x), 
  nr x # uP x (empty A) px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x : FSet A),
  apD (FSet_ind P eP lP uP assocP commP nlP nrP idemP) (nl x)
  =
  (nlP x (FSet_ind P eP lP uP assocP commP nlP nrP idemP x)
  ).

Axiom FSet_ind_beta_nr : forall
  (A : Type)
  (P : FSet A -> Type)
  (eP : P (empty A))
  (lP : forall a: A, P (L a))
  (uP : forall (x y: FSet A), P x -> P y -> P (U x y))
  (assocP : forall (x y z : FSet A) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz))
  (commP : forall (x y: FSet A) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px) 
  (nlP : forall (x : FSet A) (px: P x), 
  nl x # uP (empty A) x eP px = px)
  (nrP : forall (x : FSet A) (px: P x), 
  nr x # uP x (empty A) px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x : FSet A),
  apD (FSet_ind P eP lP uP assocP commP nlP nrP idemP) (nr x)
  =
  (nrP x (FSet_ind P eP lP uP assocP commP nlP nrP idemP x)
  ).

Axiom FSet_ind_beta_idem : forall
  (A : Type)
  (P : FSet A -> Type)
  (eP : P (empty A))
  (lP : forall a: A, P (L a))
  (uP : forall (x y: FSet A), P x -> P y -> P (U x y))
  (assocP : forall (x y z : FSet A) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz))
  (commP : forall (x y: FSet A) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px) 
  (nlP : forall (x : FSet A) (px: P x), 
  nl x # uP (empty A) x eP px = px)
  (nrP : forall (x : FSet A) (px: P x), 
  nr x # uP x (empty A) px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x : A),
  apD (FSet_ind P eP lP uP assocP commP nlP nrP idemP) (idem x)
  =
  idemP x.

Parameter A: Type.

Theorem idemSet : 
  forall x: FSet A, U x x = x.
Proof.
simple refine (FSet_ind _ _ _ _ _ _ _ _ _).
- cbn.
apply nl.
-  cbn.
apply idem.
-  cbn.
intros.
rewrite assoc.
rewrite (comm (U x y)).
rewrite assoc.
rewrite X.
rewrite <- assoc.
rewrite X0.
reflexivity.
- cbn.

(* todo optimisation *)
Theorem FSetRec (A : Type)
  (P : Type)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : FSet A) : P.
Proof.
simple refine (FSet_ind _ _ _ _ _ _ _ _ _ x).
- apply e.
- apply l.
- apply (fun _ => fun _ => u).
- cbn.
intros.
transitivity (u px (u py pz)).
apply transport_const.
apply assocP. 
- cbn.
intros.
transitivity (u px py).
apply transport_const.
apply commP.
-  cbn.
intros.
transitivity (u e px).
apply transport_const.
apply nlP.
-  cbn.
intros.
transitivity (u px e).
apply transport_const.
apply nrP.
- cbn.
intros.
transitivity (u (l x0) (l x0)).
apply transport_const.
apply idemP.
Defined.

 


Theorem FSet_rec_beta_assocT : forall
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
  (x y z : FSet A),
  ap (FSetRec e l u assocP commP nlP nrP idemP) (assoc x y z)
  =
  (assocP (FSetRec e l u assocP commP nlP nrP idemP x)
          (FSetRec e l u assocP commP nlP nrP idemP y)
          (FSetRec e l u assocP commP nlP nrP idemP z)
  ).
Proof.
intros.
eapply (cancelL (transport_const (assoc x y z) _ ) ).
simple refine 
((apD_const 
  (FSetRec e l u assocP commP nlP nrP idemP) 
  (assoc x y z))^ @ _). 
apply FSet_ind_beta_assoc. 


Theorem FSet_rec_beta_commT : forall
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
  (x y : FSet A),
  ap (FSet_rec e l u assocP commP nlP nrP idemP) (comm x y)
  =
  (commP (FSet_rec e l u assocP commP nlP nrP idemP x)
         (FSet_rec e l u assocP commP nlP nrP idemP y)
  ).

Axiom FSet_rec_beta_nl : forall
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
  (x : FSet A),
  ap (FSet_rec e l u assocP commP nlP nrP idemP) (nl x)
  =
  (nlP (FSet_rec e l u assocP commP nlP nrP idemP x)
  ).

Axiom FSet_rec_beta_nr : forall
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
  (x : FSet A),
  ap (FSet_rec e l u assocP commP nlP nrP idemP) (nr x)
  =
  (nrP (FSet_rec e l u assocP commP nlP nrP idemP x)
  ).

Axiom FSet_rec_beta_idem : forall
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
  ap (FSet_rec e l u assocP commP nlP nrP idemP) (idem x)
  =
  idemP x.


End FinSet.

Definition isIn : forall 
  (A : Type)
  (eq : A -> A -> Bool),
  A -> FSet A -> Bool.
Proof.
intro A.
intro eq.
intro a.
refine (FSet_rec A _ _ _ _ _ _ _ _ _).
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
  (A -> Bool) -> FSet A -> FSet A.
Proof.
intro A.
intro eq.
intro phi.
refine (FSet_rec A _ _ _ _ _ _ _ _ _).
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
  FSet A -> FSet A -> FSet A.
Proof.
intro A.
intro eq.
intro x.
intro y.
apply (comprehension A eq (fun (a : A) => isIn A eq a x) y).
Defined.

Definition subset (A : Type) (eq : A -> A -> Bool) (x : FSet A) (y : FSet A) : Bool.
Proof.
refine (FSet_rec A _ _ _ _ _ _ _ _ _ _).
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

Definition equal_set (A : Type) (eq : A -> A -> Bool) (x : FSet A) (y : FSet A) : Bool
  := andb (subset A eq x y) (subset A eq y x).

Fixpoint eq_nat n m : Bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat n1 m1
  end.



Theorem test : forall (A:Type) (eq : A -> A -> Bool) 
(u: FSet A), ~(u = empty _) -> exists (a: A) (v: FSet A),
u = U _ (L _ a) v /\  (isIn _ eq a v) = False.  
Proof.
intros A eq.
i





