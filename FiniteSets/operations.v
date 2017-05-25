Require Import HoTT HitTactics.
Require Import definition.
Section operations.

Context {A : Type}.
Context {A_deceq : DecidablePaths A}.

Definition isIn : A -> FSet A -> Bool.
Proof.
intros a.
hrecursion.
- exact false.
- intro a'. destruct (dec (a = a')); [exact true | exact false].
- apply orb. 
- intros x y z. compute. destruct x; reflexivity.
- intros x y. compute. destruct x, y; reflexivity.
- intros x. compute. reflexivity. 
- intros x. compute. destruct x; reflexivity.
- intros a'. compute. destruct (A_deceq a a'); reflexivity.
Defined.

Infix "∈" := isIn (at level 9, right associativity).

Definition comprehension : 
  (A -> Bool) -> FSet A -> FSet A.
Proof.
intros P.
hrecursion.
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


Definition subset :
	FSet A -> FSet A -> Bool.
Proof.
intros X Y.
hrecursion X. 
- exact true.
- exact (fun a => (a ∈ Y)).
- exact andb.
- intros. compute. destruct x; reflexivity.
- intros x y; compute; destruct x, y; reflexivity. 
- intros x; compute; destruct x; reflexivity.
- intros x; compute; destruct x; reflexivity.
- intros x; cbn; destruct (x ∈ Y); reflexivity.
Defined.

Notation "⊆" := subset.

End operations.
