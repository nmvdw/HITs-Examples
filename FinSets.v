Require Export HoTT.
Require Import HitTactics.

Module Export FinSet.
Section FSet.
Variable A : Type.

Private Inductive FSet : Type :=
  | E : FSet
  | L : A -> FSet
  | U : FSet -> FSet -> FSet.

Notation "{| x |}" :=  (L x).
Infix "∪" := U (at level 8, right associativity).
Notation "∅" := E.

Axiom assoc : forall (x y z : FSet ),
  x ∪ (y ∪ z) = (x ∪ y) ∪ z.

Axiom comm : forall (x y : FSet),
  x ∪ y = y ∪ x.

Axiom nl : forall (x : FSet),
  ∅ ∪ x = x.

Axiom nr : forall (x : FSet),
  x ∪ ∅ = x.

Axiom idem : forall (x : A),
  {| x |} ∪ {|x|} = {|x|}.

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
        | E => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => e
        | L a => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => l a
        | U y z => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => u 
           (FSet_rec P H e l u assocP commP nlP nrP idemP y)
           (FSet_rec P H e l u assocP commP nlP nrP idemP z)
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
  ap (FSet_rec P H e l u assocP commP nlP nrP idemP) (assoc x y z) 
  =
  (assocP (FSet_rec P H e l u assocP commP nlP nrP idemP x)
          (FSet_rec P H e l u assocP commP nlP nrP idemP y)
          (FSet_rec P H e l u assocP commP nlP nrP idemP z)
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
  ap (FSet_rec P H e l u assocP commP nlP nrP idemP) (comm x y)
  =
  (commP (FSet_rec P H e l u assocP commP nlP nrP idemP x)
         (FSet_rec P H e l u assocP commP nlP nrP idemP y)
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
  ap (FSet_rec P H e l u assocP commP nlP nrP idemP) (nl x)
  =
  (nlP (FSet_rec P H e l u assocP commP nlP nrP idemP x)
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
  ap (FSet_rec P H e l u assocP commP nlP nrP idemP) (nr x)
  =
  (nrP (FSet_rec P H e l u assocP commP nlP nrP idemP x)
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
  ap (FSet_rec P H e l u assocP commP nlP nrP idemP) (idem x)
  =
  idemP x.


(* Induction principle *)
Fixpoint FSet_ind
  (P : FSet -> Type)
  (H :  forall a : FSet, IsHSet (P a))
  (eP : P E)
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
  nl x # uP E x eP px = px)
  (nrP : forall (x : FSet) (px: P x), 
  nr x # uP x E px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x : FSet)
  {struct x}
  : P x
  := (match x return _ -> _ -> _ -> _ -> _ -> _ -> P x with
        | E => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => eP
        | L a => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => lP a
        | U y z => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => uP y z
           (FSet_ind P H eP lP uP assocP commP nlP nrP idemP y)
           (FSet_ind P H eP lP uP assocP commP nlP nrP idemP z)
      end) H assocP commP nlP nrP idemP.


Axiom FSet_ind_beta_assoc : forall
  (P : FSet -> Type)
  (H :  forall a : FSet, IsHSet (P a))
  (eP : P E)
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
  nl x # uP E x eP px = px)
  (nrP : forall (x : FSet) (px: P x), 
  nr x # uP x E px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x y z : FSet),
  apD (FSet_ind P H eP lP uP assocP commP nlP nrP idemP) 
      (assoc x y z)
  =
  (assocP x y z 
          (FSet_ind P H eP lP uP assocP commP nlP nrP idemP x)
          (FSet_ind P H eP lP uP assocP commP nlP nrP idemP y)
          (FSet_ind P H eP lP uP assocP commP nlP nrP idemP z)
  ).



Axiom FSet_ind_beta_comm : forall  
  (P : FSet -> Type)
  (H :  forall a : FSet, IsHSet (P a))
  (eP : P E)
  (lP : forall a: A, P (L a))
  (uP : forall (x y: FSet), P x -> P y -> P (U x y))
  (assocP : forall (x y z : FSet) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz))
  (commP : forall (x y : FSet) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px) 
  (nlP : forall (x : FSet) (px: P x), 
  nl x # uP E x eP px = px)
  (nrP : forall (x : FSet) (px: P x), 
  nr x # uP x E px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x y : FSet),
  apD (FSet_ind P H eP lP uP assocP commP nlP nrP idemP) (comm x y)
  =
  (commP x y 
         (FSet_ind P H eP lP uP assocP commP nlP nrP idemP x)
         (FSet_ind P H eP lP uP assocP commP nlP nrP idemP y)
  ).

Axiom FSet_ind_beta_nl : forall
  (P : FSet -> Type)
  (H :  forall a : FSet, IsHSet (P a))
  (eP : P E)
  (lP : forall a: A, P (L a))
  (uP : forall (x y: FSet), P x -> P y -> P (U x y))
  (assocP : forall (x y z : FSet) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz))
  (commP : forall (x y : FSet) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px) 
  (nlP : forall (x : FSet) (px: P x), 
  nl x # uP E x eP px = px)
  (nrP : forall (x : FSet) (px: P x), 
  nr x # uP x E px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x : FSet),
  apD (FSet_ind P H eP lP uP assocP commP nlP nrP idemP) (nl x)
  =
  (nlP x (FSet_ind P H eP lP uP assocP commP nlP nrP idemP x)
  ).

Axiom FSet_ind_beta_nr : forall
  (P : FSet -> Type)
  (H :  forall a : FSet, IsHSet (P a))
  (eP : P E)
  (lP : forall a: A, P (L a))
  (uP : forall (x y: FSet), P x -> P y -> P (U x y))
  (assocP : forall (x y z : FSet) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz))
  (commP : forall (x y : FSet) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px) 
  (nlP : forall (x : FSet) (px: P x), 
  nl x # uP E x eP px = px)
  (nrP : forall (x : FSet) (px: P x), 
  nr x # uP x E px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x : FSet),
  apD (FSet_ind P H eP lP uP assocP commP nlP nrP idemP) (nr x)
  =
  (nrP x (FSet_ind P H eP lP uP assocP commP nlP nrP idemP x)
  ).

Axiom FSet_ind_beta_idem : forall
  (P : FSet -> Type)
  (H :  forall a : FSet, IsHSet (P a))
  (eP : P E)
  (lP : forall a: A, P (L a))
  (uP : forall (x y: FSet), P x -> P y -> P (U x y))
  (assocP : forall (x y z : FSet) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz))
  (commP : forall (x y : FSet) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px) 
  (nlP : forall (x : FSet) (px: P x), 
  nl x # uP E x eP px = px)
  (nrP : forall (x : FSet) (px: P x), 
  nr x # uP x E px eP = px)
  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x)
  (x : A),
  apD (FSet_ind P H eP lP uP assocP commP nlP nrP idemP) (idem x)
  =
  idemP x.

End FSet.

(* TODO: add an induction principle *)
Definition FSetCL A : HitRec.class (FSet A) _ _ := 
   HitRec.Class (FSet A) (fun x P H e l u aP cP lP rP iP => FSet_rec A P H e l u aP cP lP rP iP x) (fun x P H e l u aP cP lP rP iP => FSet_ind A P H e l u aP cP lP rP iP x).
Canonical Structure FSetTy A : HitRec.type := HitRec.Pack _ _ _ (FSetCL A).

Arguments E {_}.
Arguments U {_} _ _.
Arguments L {_} _.

End FinSet.

Section functions.
Parameter A : Type.
Parameter eq : A -> A -> Bool.
Parameter eq_refl: forall a:A, eq a a = true.

Definition isIn : A -> FSet A -> Bool.
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
  (A -> Bool) -> FSet A -> FSet A.
Proof.
intros P X.
hrecursion X.
- apply E.
- intro a.
  refine (if (P a) then L a else E).
- apply U.
- intros. cbv. apply assoc.
- intros. cbv. apply comm.
- intros. cbv. apply nl.
- intros. cbv. apply nr.
- intros. cbv. 
  destruct (P x); simpl.
  + apply idem.
  + apply nl.
Defined.
Require Import FunextAxiom.
Lemma comprehension_idem: 
   forall (X:FSet A), forall Y, comprehension (fun x => isIn x (U X Y)) X = X.
Proof.
simple refine (FSet_ind _ _ _ _ _ _ _ _ _ _ _); simpl.
- intro Y. cbv. reflexivity.
- intros a Y. unfold comprehension. unfold HitRec.hrecursion. simpl.
  enough (isIn a (U (L a) Y) = true).
  + rewrite X. reflexivity.
  + unfold isIn. unfold HitRec.hrecursion. simpl.
    rewrite eq_refl. auto.
- intros X1 X2 IH1 IH2 Y.
  unfold comprehension. unfold  HitRec.hrecursion. simpl.
  rewrite <- (assoc _ X1 X2 Y).
  f_ap. 
  + apply (IH1 (U X2 Y)).
  + rewrite (assoc _ X1 X2 Y).
    rewrite (comm _ X1 X2).
    rewrite <- (assoc _ X2 X1 Y).
    apply (IH2 (U X1 Y)).
Admitted.


Definition intersection : 
  FSet A -> FSet A -> FSet A.
Proof.
intros X Y.
apply (comprehension (fun (a : A) => isIn a X) Y).
Defined.

Definition subset (x : FSet A) (y : FSet A) : Bool.
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


Definition subset' (x : FSet A) (y : FSet A) : Bool.
Proof.
refine (FSet_rec A _ _ _ _ _ _ _ _ _ _).
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

Definition equal_set (x : FSet A) (y : FSet A) : Bool
  := andb (subset x y) (subset y x).

Fixpoint eq_nat n m : Bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat n1 m1
  end.

End functions.