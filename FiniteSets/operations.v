Require Import HoTT.
Require Export HoTT.
Require Import definition.
(*Set Implicit Arguments.*)
Arguments E {_}.
Arguments U {_} _ _.
Arguments L {_} _.
Arguments assoc {_} _ _ _.
Arguments comm {_} _ _.
Arguments nl {_} _.
Arguments nr {_} _.
Arguments idem {_} _.

Section operations.

Variable A : Type.
Parameter A_eqdec : forall (x y : A), Decidable (x = y).
Definition deceq (x y : A) :=
  if dec (x = y) then true else false.

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

Infix "∈" := isIn (at level 9, right associativity).

Definition comprehension : 
  (A -> Bool) -> FSet A -> FSet A.
Proof.
intros P.
simple refine (FSet_rec A _ _ _ _ _ _ _ _ _ _).
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

Definition intersection : 
  FSet A -> FSet A -> FSet A.
Proof.
intros X Y.
apply (comprehension (fun (a : A) => isIn a X) Y).
Defined.

End operations.