Require Import HoTT.
Require Import HitTactics.
Require Import definition.
Require Import operations.
Require Import properties.
Require Import empty_set.


Module Export FSetC.
 
Section FSetC.
Variable A : Type.

Private Inductive FSetC : Type :=
  | Nil : FSetC
  | Cns : A ->  FSetC -> FSetC.

Infix ";;" := Cns (at level 8, right associativity).
Notation "∅" := Nil.

Axiom dupl : forall (a: A) (x: FSetC),
  a ;; a ;; x = a ;; x. 

Axiom comm : forall (a b: A) (x: FSetC),
   a ;; b ;; x = b ;; a ;; x.

Axiom trunc : IsHSet FSetC.

End FSetC.

Arguments Nil {_}.
Arguments Cns {_} _ _.
Arguments dupl {_} _ _.
Arguments comm {_} _ _ _.

Infix ";;" := Cns (at level 8, right associativity).
Notation "∅" := Nil.

Section FSetC_induction.

Variable A: Type.
Variable (P : FSetC A -> Type).
Variable (H :  forall x : FSetC A, IsHSet (P x)).
Variable (eP : P ∅).
Variable (cnsP : forall (a:A) (x: FSetC A), P x -> P (a ;; x)).
Variable (duplP : forall (a: A) (x: FSetC A) (px : P x),
	          dupl a x # cnsP a (a;;x) (cnsP a x px) = cnsP a x px).
Variable (commP : forall (a b: A) (x: FSetC A) (px: P x),
			     comm a b x # cnsP a (b;;x) (cnsP b x px) = 
			     cnsP b (a;;x) (cnsP a x px)).
			     
(* Induction principle *)
Fixpoint FSetC_ind
  (x : FSetC A)
  {struct x}
  : P x
  := (match x return _ -> _ -> _ -> P x with
        | Nil => fun _ => fun _ => fun _  => eP
        | a ;; y => fun _ => fun _ => fun _ => cnsP a y (FSetC_ind y)
      end) H duplP commP.


Axiom FSetC_ind_beta_dupl : forall (a: A) (x : FSetC A),
  apD FSetC_ind (dupl a x) = 	duplP a x (FSetC_ind x).

Axiom FSetC_ind_beta_comm : forall (a b: A) (x : FSetC A),
  apD FSetC_ind (comm a b x) = commP a b x (FSetC_ind x).

End FSetC_induction.

Section FSetC_recursion.

Variable A: Type.
Variable (P: Type).
Variable (H: IsHSet P).
Variable (nil : P).
Variable (cns :  A -> P -> P).
Variable (duplP : forall (a: A) (x: P), cns a (cns a x) = (cns a x)).
Variable (commP : forall (a b: A) (x: P), cns a (cns b x) = cns b (cns a x)).

(* Recursion principle *)
Definition FSetC_rec : FSetC A -> P.
Proof.
simple refine (FSetC_ind _ _ _ _ _  _ _ ); 
try (intros; simple refine ((transport_const _ _) @ _ ));  cbn.
- apply nil.
- apply 	(fun a => fun _ => cns a). 
- apply duplP.
- apply commP. 
Defined.


Definition FSetC_rec_beta_dupl : forall (a: A) (x : FSetC A),
  ap FSetC_rec (dupl a x) = duplP a (FSetC_rec x).
Proof.
intros. 
unfold FSet_rec.
eapply (cancelL (transport_const (dupl a x) _)).
simple refine ((apD_const _ _)^ @ _).
apply FSetC_ind_beta_dupl.
Defined.

Definition FSetC_rec_beta_comm : forall (a b: A) (x : FSetC A),
  ap FSetC_rec (comm a b x) = commP a b (FSetC_rec x).
Proof.
intros. 
unfold FSet_rec.
eapply (cancelL (transport_const (comm a b x) _)).
simple refine ((apD_const _ _)^ @ _).
apply FSetC_ind_beta_comm.
Defined.

End FSetC_recursion.


Instance FSetC_recursion A : HitRecursion (FSetC A) := {
  indTy := _; recTy := _; 
  H_inductor := FSetC_ind A; H_recursor := FSetC_rec A }.





Section Append.

Context {A : Type}.
Context {A_deceq : DecidablePaths A}.

Definition append  (x y: FSetC A) : FSetC A.
hinduction x.
- apply y.
- apply Cns.
- apply dupl.
- apply comm.
Defined.


Lemma append_nl: 
  forall (x: FSetC A), append ∅ x = x. 
Proof.
  intro. reflexivity.
Defined.

Lemma append_nr: 
  forall (x: FSetC A), append x ∅ = x.
Proof.
  hinduction; try (intros; apply set_path2).
  -  reflexivity.
  -  intros. apply (ap (fun y => a ;; y) X).
Defined.
 
Lemma append_assoc {H: Funext}:  
  forall (x y z: FSetC A), append x (append y z) = append (append x y) z.
Proof.
  intro x; hinduction x; try (intros; apply set_path2).
  - reflexivity.
  - intros a x HR y z. 
    specialize (HR y z).
    apply (ap (fun y => a ;; y) HR). 
  - intros. apply path_forall. 
  	  intro. apply path_forall. 
  	  intro. apply set_path2.
  - intros. apply path_forall.
    intro. apply path_forall. 
  	  intro. apply set_path2.
Defined.
      
 Lemma aux: forall (a: A) (x: FSetC A), 
   a ;; x = append x (a ;; ∅).
Proof.
intro a. hinduction; try (intros; apply set_path2).
- reflexivity.
- intros b x HR. refine (_ @ _).
	+ apply comm.
	+ apply (ap (fun y => b ;; y) HR).
Defined.


Lemma append_comm {H: Funext}: 
  forall (x1 x2: FSetC A), append x1 x2 = append x2 x1.
Proof.
  intro x1. 
  hinduction x1;  try (intros; apply set_path2).
  - intros. symmetry. apply append_nr. 
  - intros a x1 HR x2.
    etransitivity.
    apply (ap (fun y => a;;y) (HR x2)).  
    transitivity  (append (append x2 x1) (a;;∅)).
    + apply aux. 
    + etransitivity.
    	  * symmetry. apply append_assoc.
    	  * simple refine (ap (fun y => append x2 y) (aux _ _)^).
  - intros. apply path_forall.
    intro. apply set_path2.
  - intros. apply path_forall.
    intro. apply set_path2.  
Defined.


End Append.


Section Singleton.

Context {A : Type}.
Context {A_deceq : DecidablePaths A}.

Definition singleton (a:A) : FSetC A := a;;∅.

Lemma singleton_idem: forall (a: A), 
  append (singleton a) (singleton a) = singleton a.
Proof.
unfold singleton. intro. cbn. apply dupl.
Defined.

End Singleton.



Infix ";;" := Cns (at level 8, right associativity).
Notation "∅" := Nil.

End FSetC.


Section Iso.

Context {A : Type}.
Context {A_deceq : DecidablePaths A}.
Context {H : Funext}.


Definition FSetC_to_FSet: FSetC A -> FSet A.
Proof.
hrecursion.
- apply E.
- intros a x. apply (U (L a) x).
- intros. cbn.  
	etransitivity. apply assoc.
	apply (ap (fun y => U y x)).
	apply idem.
- intros. cbn.
 etransitivity. apply assoc.
 etransitivity. refine (ap (fun y => U y x) _ ).
 apply FSet.comm.
 symmetry. 
 apply assoc.
Defined.

Definition FSet_to_FSetC: FSet A -> FSetC A :=
  FSet_rec A (FSetC A) (trunc A) ∅ singleton append append_assoc 
    append_comm append_nl append_nr singleton_idem.


Lemma append_union: forall (x y: FSetC A), 
  FSetC_to_FSet (append x y) = U (FSetC_to_FSet x) (FSetC_to_FSet y).
Proof.
intros x. 
hrecursion x; try (intros; apply path_forall; intro; apply set_path2).
- intros. symmetry. apply nl.
- intros a x HR y. rewrite HR. apply assoc.
Defined.

Lemma repr_iso_id_l: forall (x: FSet A), FSetC_to_FSet (FSet_to_FSetC x) = x.
Proof.
hinduction; try (intros; apply set_path2).
- reflexivity.
- intro. apply nr.
- intros x y p q. rewrite append_union, p, q. reflexivity.
Defined.


Lemma repr_iso_id_r: forall (x: FSetC A), FSet_to_FSetC (FSetC_to_FSet x) = x.
Proof.
hinduction; try (intros; apply set_path2).
- reflexivity.
- intros a x HR. rewrite HR. reflexivity.
Defined.


Theorem repr_iso: FSet A <~> FSetC A.
Proof.
simple refine (@BuildEquiv (FSet A) (FSetC A) FSet_to_FSetC _ ).
apply isequiv_biinv.
unfold BiInv. split.
exists FSetC_to_FSet.
unfold Sect. apply repr_iso_id_l.
exists FSetC_to_FSet.
unfold Sect. apply repr_iso_id_r.
Defined.

End Iso.

Section Length.

Context {A : Type}.
Context {A_deceq : DecidablePaths A}.
Context {H : Funext}.

Definition length (x: FSetC A) : nat.
Proof.
simple refine (FSetC_ind A _ _ _ _ _ _ x ); simpl.
- exact 0.
- intros a y n. 
  pose (y' := FSetC_to_FSet y).
  exact (if isIn a y' then n else (S n)).
- intros. rewrite transport_const. cbn. 
  destruct (dec (a = a)); cbn. reflexivity.
  destruct n; reflexivity.
- intros. rewrite transport_const. cbn.
  destruct (dec (a = b)), (dec (b = a)); cbn. 
  + rewrite p. reflexivity.
  + contradiction (n p^).
  + contradiction (n p^).
  + intros. 
  destruct (a ∈ (FSetC_to_FSet x0)), (b ∈ (FSetC_to_FSet x0)); reflexivity.
Defined.

Definition length_FSet (x: FSet A) := length (FSet_to_FSetC x).

Lemma length_singleton: forall (a: A), length_FSet (L a) = 1.
Proof. 
intro a.
cbn. reflexivity. 
Defined.

End Length.





