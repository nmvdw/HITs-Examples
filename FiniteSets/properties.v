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
  
Theorem deceq_sym : forall x y, operations.deceq A x y = operations.deceq A y x.
Proof.
intros x y.
unfold operations.deceq.
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

Theorem absorbtion_1 : forall (X1 X2 Y : FSet A),
    intersection (U X1 X2) Y = U (intersection X1 Y) (intersection X2 Y).
Admitted.

Theorem intersection_La : forall (a : A) (X : FSet A),
    intersection (L a) X = if isIn a X then L a else E.
Proof.
intro a.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; try (intros ; apply set_path2).
- reflexivity.
- intro b.
  cbn.
  rewrite deceq_sym.
  unfold operations.deceq.
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

Theorem intersection_isIn : forall a (x y: FSet A),
    isIn a (intersection x y) = andb (isIn a x) (isIn a y).
Proof.
intros a x y.
simple refine (FSet_ind A (fun z => isIn a (intersection z y) = andb (isIn a z) (isIn a y)) _ _ _ _ _ _ _ _ _ x) ; try (intros ; apply set_path2) ; cbn.
- rewrite intersection_0l.
  reflexivity.
- intro b.
  rewrite intersection_La.
  unfold operations.deceq.
  destruct (dec (a = b)) ; cbn.
  * rewrite p.
    destruct (isIn b y).
    + cbn.
      unfold operations.deceq.
      destruct (dec (b = b)).
      { reflexivity. }
      { pose (n idpath). contradiction. }
    + reflexivity.
  * destruct (isIn b y).
    + cbn.
      unfold operations.deceq.
      destruct (dec (a = b)).
      { pose (n p). contradiction. }
      { reflexivity. }
    + reflexivity.
- intros X1 X2 P Q.
  rewrite absorbtion_1.
  cbn.
  rewrite P.
  rewrite Q.
  destruct (isIn a X1) ; destruct (isIn a X2) ; destruct (isIn a y) ; reflexivity.
Defined.

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

Theorem intersection_assoc (X Y Z: FSet A) :
    intersection X (intersection Y Z) = intersection (intersection X Y) Z.
Proof.
simple refine
  (FSet_ind A
    (fun z => intersection z (intersection Y Z) = intersection (intersection z Y) Z)
     _ _ _ _ _ _ _ _ _ X) ; try (intros ; apply set_path2).
- cbn.
  rewrite intersection_0l.
  rewrite intersection_0l.
  rewrite intersection_0l.
  reflexivity.
- intros a.
  cbn.
  rewrite intersection_La.
  rewrite intersection_La.
  rewrite intersection_isIn.
  destruct (isIn a Y).
  * rewrite intersection_La.
    destruct (isIn a Z).
    + reflexivity.
    + reflexivity.
  * rewrite intersection_0l.
    reflexivity.      
- unfold intersection. cbn.
  intros X1 X2 P Q.
  rewrite comprehension_or.
  rewrite P.
  rewrite Q.
  rewrite comprehension_or.
  cbn.
  rewrite comprehension_or.
  reflexivity.
Defined.

Theorem comprehension_subset : forall ϕ (X : FSet A),
    U (comprehension ϕ X) X = X.
Proof.
intros ϕ.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; try (intros ; apply set_path2) ; cbn.
- apply nl.
- intro a.
  destruct (ϕ a).
  * apply union_idem.
  * apply nl.
- intros X Y P Q.
  rewrite assoc.
  rewrite <- (assoc (comprehension ϕ X) (comprehension ϕ Y) X).
  rewrite (comm (comprehension ϕ Y) X).
  rewrite assoc.
  rewrite P.
  rewrite <- assoc.
  rewrite Q.
  reflexivity.
Defined.

Theorem intersection_idem : forall (X : FSet A), intersection X X = X.
Proof.
simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _) ; try (intros ; apply set_path2) ; cbn.
- reflexivity.
- intro a.
  unfold operations.deceq.
  destruct (dec (a = a)).
  * reflexivity.
  * contradiction (n idpath).
- intros X Y IHX IHY.
  cbn in *.
  rewrite comprehension_or.
  rewrite comprehension_or.
  unfold intersection in *.
  rewrite IHX.  
  rewrite IHY.
  rewrite comprehension_subset.
  rewrite (comm X).
  rewrite comprehension_subset.
  reflexivity.
Defined.
  

End properties. 
