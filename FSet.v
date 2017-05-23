Require Import HoTT.
Require Export HoTT.
Require Import FunextAxiom.

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

Parameter A : Type.
Parameter A_eqdec : forall (x y : A), Decidable (x = y).
Definition deceq (x y : A) :=
  if dec (x = y) then true else false.

Theorem deceq_sym : forall x y, deceq x y = deceq y x.
Proof.
intros x y.
unfold deceq.
destruct (dec (x = y)) ; destruct (dec (y = x)) ; cbn.
- reflexivity. 
- pose (n (p^)) ; contradiction.
- pose (n (p^)) ; contradiction.
- reflexivity.
Defined.

Arguments E {_}.
Arguments U {_} _ _.
Arguments L {_} _.

Theorem idemU : forall x : FSet A, U x x = x.
Proof.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; try (intros ; apply set_path2) ; cbn.
- apply nl.
- apply idem.
- intros x y P Q.
  etransitivity. apply assoc.  
  etransitivity. apply (ap (fun p => U (U p x) y) (comm A x y)).
  etransitivity. apply (ap (fun p => U p y) (assoc A y x x))^.
  etransitivity. apply (ap (fun p => U (U y p) y) P).
  etransitivity. apply (ap (fun p => U p y) (comm A y x)).
  etransitivity. apply (assoc A x y y)^.
  apply (ap (fun p => U x p) Q).
Defined.
  
Definition isIn : A -> FSet A -> Bool.
Proof.
intros a.
simple refine (FSet_rec A _ _ _ _ _ _ _ _ _ _).
- exact false.
- intro a'. apply (deceq a a').
- apply orb. 
- intros x y z. destruct x; reflexivity.
- intros x y. destruct x, y; reflexivity.
- intros x. reflexivity. 
- intros x. destruct x; reflexivity.
- intros a'. destruct (deceq a a'); reflexivity.
Defined.

Definition comprehension : 
  (A -> Bool) -> FSet A -> FSet A.
Proof.
intros P.
simple refine (FSet_rec A _ _ _ _ _ _ _ _ _ _).
- apply E.
- intro a.
  refine (if (P a) then L a else E).
- apply U.
- intros. apply assoc.
- intros. apply comm.
- intros. apply nl.
- intros. apply nr.
- intros. cbn.  
  destruct (P x).
  + apply idem.
  + apply nl.
Defined.

Theorem comprehension_or : forall ϕ ψ x,
    comprehension (fun a => orb (ϕ a) (ψ a)) x = U (comprehension ϕ x) (comprehension ψ x).
Proof.
intros ϕ ψ.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; try (intros ; apply set_path2). 
- cbn. symmetry ; apply nl.
- cbn. intros.
  destruct (ϕ a) ; destruct (ψ a) ; symmetry.
  * apply idem.
  * apply nr. 
  * apply nl.
  * apply nl.
- simpl. intros x y P Q.
  cbn. 
  rewrite P.
  rewrite Q.
  rewrite <- assoc.
  rewrite (assoc A (comprehension ψ x)).
  rewrite (comm A (comprehension ψ x) (comprehension ϕ y)).
  rewrite <- assoc.
  rewrite <- assoc.
  reflexivity.
Defined.

Definition intersection (X Y : FSet A) : FSet A := comprehension (fun (a : A) => isIn a X) Y.

Theorem intersection_idem : forall x, intersection x x = x.
Proof.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; try (intros ; apply set_path2) ; cbn.
- reflexivity.
- intro a.
  unfold deceq.
  destruct (dec (a = a)).
  * reflexivity.
  * pose (n idpath) ; contradiction.
- intros x y P Q.
  rewrite comprehension_or.
  rewrite comprehension_or.
  unfold intersection in P.
  unfold intersection in Q.
  rewrite P.
  rewrite Q.
Admitted.
    
  
    

Theorem intersection_EX : forall x,
    intersection E x = E.
Proof.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; try (intros ; apply set_path2).
- reflexivity.
- intro a.
  reflexivity.
- unfold intersection.
  intros x y P Q.
  cbn.
  rewrite P.
  rewrite Q.
  apply nl.
Defined.

Definition intersection_XE x : intersection x E = E := idpath.

Theorem intersection_La : forall a x,
    intersection (L a) x = if isIn a x then L a else E.
Proof.
intro a.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; try (intros ; apply set_path2).
- reflexivity.
- intro b.
  cbn.
  rewrite deceq_sym.
  unfold deceq.
  destruct (dec (a = b)).
  * rewrite p ; reflexivity.
  * reflexivity.
- unfold intersection.
  intros x y P Q.
  cbn.
  rewrite P.
  rewrite Q.
  destruct (isIn a x) ; destruct (isIn a y).
  * apply idem.
  * apply nr.
  * apply nl. 
  * apply nl.
Defined.


(*
Theorem intersection_comm : forall x y,
    intersection x y = intersection y x.
Proof.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; cbn.
- intros.
  rewrite intersection_E.  
  reflexivity.
- intros a.
  simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; cbn.
  * reflexivity.
  * intro b.
    admit.
  * intros x y.
    destruct (isIn a x) ; destruct (isIn a y) ; intros P Q.
  + rewrite P.
    *)
            

Theorem comp_false : forall x,
    comprehension (fun _ => false) x = E.
Proof.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; try (intros ; apply set_path2) ; cbn.
- reflexivity.
- intro a ; reflexivity.
- intros x y P Q.
  rewrite P.
  rewrite Q.
  apply nl.
Defined.

(*Theorem union_dist : forall x y z,
    intersection z (U x y) = U (intersection z x) (intersection z y).
Proof.
intros x y.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; cbn.
- rewrite intersection_E.
  rewrite intersection_E.
  rewrite comp_false.
  rewrite comp_false.
  reflexivity.
- intro a. 
  *)

Theorem union_dist : forall x y z,
    intersection (U x y) z = U (intersection x z) (intersection y z).
Proof.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; cbn.
- intros.
  rewrite nl.
  rewrite intersection_EX.
  rewrite nl.
  reflexivity.
- intro a.
  simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; cbn.
  * intros.
    rewrite nr.
    rewrite intersection_EX.
    rewrite nr.
    reflexivity.
  * intros b.
    simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; cbn.
    + rewrite nl. reflexivity.
    + intros c.
      unfold deceq.
      destruct (dec (c = a)) ; destruct (dec (c = b)) ; cbn.
      { rewrite idem. reflexivity. }
      { rewrite nr. reflexivity. }
      { rewrite nl. reflexivity. }
      { rewrite nl. reflexivity. }
    + intros x y P Q.
      rewrite comprehension_or.
      rewrite comprehension_or.
      rewrite assoc.
      rewrite <- (assoc A (comprehension (fun a0 : A => deceq a0 a) x) (comprehension (fun a0 : A => deceq a0 b) x)).
      rewrite (comm A (comprehension (fun a0 : A => deceq a0 b) x) (comprehension (fun a0 : A => deceq a0 a) y)).
      rewrite assoc.
      rewrite <- assoc.
      reflexivity.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  * intros x y P Q z.
    cbn.
    
Admitted.

Theorem intersection_isIn : forall a x y,
    isIn a (intersection x y) = andb (isIn a x) (isIn a y).
Proof.
intros a.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; cbn.
- intros y.
  rewrite intersection_EX.
  reflexivity.
- intros b y.
  rewrite intersection_La.
  unfold deceq.
  destruct (dec (a = b)) ; cbn.
  * rewrite p.
    destruct (isIn b y).
    + cbn.
      unfold deceq.
      destruct (dec (b = b)).
      { reflexivity. }
      { pose (n idpath). contradiction. }
    + reflexivity.
  * destruct (isIn b y).
    + cbn.
      unfold deceq.
      destruct (dec (a = b)).
      { pose (n p). contradiction. }
      { reflexivity. }
    + reflexivity.
- intros x y P Q z.
  rewrite union_dist.
  cbn.
  rewrite P.
  rewrite Q.
  destruct (isIn a x) ; destruct (isIn a y) ; destruct (isIn a z) ; reflexivity.
Admitted.

Theorem intersection_assoc x y z :
    intersection x (intersection y z) = intersection (intersection x y) z.
Proof.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _ x) ; cbn ;  try (intros ; apply set_path2).
- intros.
  exact _.
- cbn.
  rewrite intersection_E.
  rewrite intersection_E.
  rewrite intersection_E.
  reflexivity.
- intros a y z.
  cbn.
  rewrite intersection_La.
  rewrite intersection_La.
  rewrite intersection_isIn.
  destruct (isIn a y).
  * rewrite intersection_La.
    destruct (isIn a z).
    + reflexivity.
    + reflexivity.
  * rewrite intersection_E.
    reflexivity.      
- unfold intersection. cbn.
  intros x y P Q z z'.
  rewrite comprehension_or.
  rewrite P.
  rewrite Q.
  rewrite comprehension_or.
  cbn.
  rewrite comprehension_or.
  reflexivity.
Admitted.
