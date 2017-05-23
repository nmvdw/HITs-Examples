Require Import HoTT.
Require Export HoTT.
Require Import definition.
Require Import operations.
Section properties.

Arguments E {_}.
Arguments U {_} _ _.
Arguments L {_} _.
Arguments assoc {_} _ _ _.
Arguments comm {_} _ _.
Arguments nl {_} _.
Arguments nr {_} _.
Arguments idem {_} _.
Arguments isIn {_} _ _.
Arguments comprehension {_} _ _.
Arguments intersection {_} _ _.

Variable A : Type.
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
  
 
Lemma comprehension_false: forall Y: FSet A, 
	    comprehension (fun a => isIn a E) Y = E.
Proof.
simple refine (FSet_ind _ _ _ _ _ _ _ _ _ _ _); 
try (intros; apply set_path2).
- cbn. reflexivity.
- cbn. reflexivity.
- intros x y IHa IHb.
  cbn.
  rewrite IHa.
  rewrite IHb.
  rewrite nl.
  reflexivity.
Defined.


Lemma isIn_singleton_eq (a b: A) : isIn a  (L b) = true -> a = b.
Proof. unfold isIn. simpl. unfold operations.deceq.
destruct (dec (a = b)). intro. apply p.
intro X. 
contradiction (false_ne_true X).
Defined.

Lemma isIn_empty_false (a: A) : isIn a E = true -> Empty.
Proof. 
cbv. intro X.
contradiction (false_ne_true X). 
Defined.

Lemma isIn_union (a: A) (X Y: FSet A) : 
	    isIn a (U X Y) = (isIn a X || isIn a Y)%Bool.
Proof. reflexivity. Qed. 


Theorem comprehension_or : forall ϕ ψ (x: FSet A),
    comprehension (fun a => orb (ϕ a) (ψ a)) x = U (comprehension ϕ x) 
    (comprehension ψ x).
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
  rewrite (assoc  (comprehension ψ x)).
  rewrite (comm  (comprehension ψ x) (comprehension ϕ y)).
  rewrite <- assoc.
  rewrite <- assoc.
  reflexivity.
Defined.

Theorem intersection_isIn : forall a (x y: FSet A),
    isIn a (intersection x y) = andb (isIn a x) (isIn a y).
Proof.
Admitted.
(*
intros a.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; cbn.
- intros y.
  rewrite intersection_E.
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
  enough (intersection (U x y) z = U (intersection x z) (intersection y z)).
  rewrite X.
  cbn.
  rewrite P.
  rewrite Q.
  destruct (isIn a x) ; destruct (isIn a y) ; destruct (isIn a z) ; reflexivity.
  admit.
Admitted.
*)


Theorem union_idem : forall x: FSet A, U x x = x.
Proof.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; 
try (intros ; apply set_path2) ; cbn.
- apply nl.
- apply idem.
- intros x y P Q.
  rewrite assoc.
  rewrite (comm x y).
  rewrite <- (assoc y x x).
  rewrite P.
  rewrite (comm y x).
  rewrite <- (assoc x y y).
  rewrite Q.
  reflexivity.
Defined.

Lemma intersection_0l: forall X: FSet A, intersection E X = E.
Proof.       
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; 
try (intros ; apply set_path2).
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

Definition intersection_0r (X: FSet A): intersection X E = E := idpath.


     

Lemma intersection_comm (X Y: FSet A): intersection X Y = intersection Y X.
Proof.
(*
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _ X) ;  
try (intros; apply set_path2).
- cbn. unfold intersection. apply comprehension_false.
- cbn. unfold intersection. intros a.
  hrecursion Y; try (intros; apply set_path2).
  + cbn. reflexivity.
  + cbn. intros.
  		destruct  (dec (a0 = a)). 
  		rewrite p. destruct (dec (a=a)).
  		reflexivity.
  		contradiction n. 
  		reflexivity. 
		destruct  (dec (a = a0)).
		contradiction n. apply p^. reflexivity.
 	+ cbn -[isIn]. intros Y1 Y2 IH1 IH2.
 	 	rewrite IH1. 
 	 	rewrite IH2. 	 	
 	 	apply 	(comprehension_union (L a)).
- intros X1 X2 IH1 IH2.
  cbn.
  unfold intersection in *.
  rewrite <- IH1.
  rewrite <- IH2. symmetry.
	apply comprehension_union.
Defined.*)
Admitted.

Lemma comprehension_union (X Y Z: FSet A) : 
	U (comprehension (fun a => isIn a Y) X)
	  (comprehension (fun a => isIn a Z) X) =
	  comprehension (fun a => isIn a (U Y Z)) X.
Proof.
Admitted.
(*
hrecursion X; try (intros; apply set_path2).
- cbn. apply nl.
- cbn. intro a. 
		destruct (isIn a Y); simpl;
		destruct (isIn a Z); simpl.
		apply idem.
		apply nr.
		apply nl.
		apply nl.
- cbn. intros X1 X2 IH1 IH2.
	rewrite assoc.
	rewrite (comm _ (comprehension (fun a : A => isIn a Y) X1) 
				  (comprehension (fun a : A => isIn a Y) X2)).
  rewrite <- (assoc _   
  				  (comprehension (fun a : A => isIn a Y) X2)
       		 (comprehension (fun a : A => isIn a Y) X1)
       		 (comprehension (fun a : A => isIn a Z) X1)
       		 ).
  rewrite IH1.
  rewrite comm.
  rewrite assoc. 
  rewrite (comm _ (comprehension (fun a : A => isIn a Z) X2) _).
  rewrite IH2.
  apply comm.
Defined.*)

Theorem intersection_assoc : forall (x y z: FSet A),
    intersection x (intersection y z) = intersection (intersection x y) z.
Admitted.
(*
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; try (intros ; apply set_path2).
- intros y z.
  cbn.
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
*)

End properties.
  
