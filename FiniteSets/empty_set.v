Require Import HoTT.
Require Import HitTactics.
Require Import definition.
Require Import operations.
Require Import properties.


Ltac destruct_match := repeat
  match goal with
  | [|- match ?X with | _ => _ end ] => destruct X
 	end.
 	
Ltac destruct_match_1 :=
	repeat match goal with
    | [|- match ?X with | _ => _ end ] => destruct X
    | [|- ?X = ?Y ] => apply path_ishprop
    | [ H: ?x <> E  |- Empty ] => destruct H
    | [  H1: ?x = E, H2: ?y = E, H3: ?w ∪ ?q  = E |- ?r = E]
    			=> rewrite H1, H2 in H3; rewrite nl in H3;  rewrite nl in H3
  end.

Ltac eq_neq_tac :=
match goal  with
    |  [ H: ?x <> E, H': ?x = E |- _ ] => destruct H; assumption
end.

Section EmptySetProperties.

Context {A : Type}.
Context {A_deceq : DecidablePaths A}.


(*Should go to properties *)
Lemma union_subset `{Funext} : 
	forall x y z: FSet A, x ∪ y ⊆ z = true -> x ⊆ z = true /\ y ⊆ z = true.
intros x y z Hu.
split.
- eapply subset_isIn. intros a Ha.
  eapply subset_isIn in Hu.
  + instantiate (1 := a) in Hu.
  assumption.
  + transitivity (a ∈ x || a ∈ y)%Bool . 
  apply union_isIn.
  rewrite Ha. cbn; reflexivity.
- eapply subset_isIn. intros a Ha.
  eapply subset_isIn in Hu.
  + instantiate (1 := a) in Hu.
  assumption.
  + rewrite comm. transitivity (a ∈ y || a ∈ x)%Bool . 
  apply union_isIn.
  rewrite Ha. cbn. reflexivity.
Defined.
 

Lemma eset_subset_l `{Funext} : forall x: FSet A, x ⊆ ∅ = true -> x = ∅.
intros x He. 
apply eq_subset. 
split.
- cbn; reflexivity.
- assumption.
Defined.

Lemma eset_subset_r `{Funext} : forall x: FSet A,  x = ∅ -> x ⊆ ∅ = true.
intros x He. 
apply eq_subset. apply symmetry. assumption.
Defined.

Lemma subset_transitive `{Funext}: 
	forall x y z, x ⊆ y = true -> y ⊆ z = true -> x ⊆ z = true.
intros.
Admitted.

Lemma eset_union_l `{Funext}  : forall x y: FSet A, x ∪ y = ∅ -> x = ∅ .
Proof.
intros.
assert (x ⊆ (x  ∪ y) = true).
apply subset_union_equiv. rewrite assoc. rewrite (union_idem x). reflexivity.
apply eset_subset_r in X.
assert (x ⊆ ∅ = true).
apply (subset_transitive x (U x y)); assumption.
apply eset_subset_l.
assumption.
Defined.

Lemma eset_union_lr `{Funext}  : 
forall x y: FSet A, x ∪ y = ∅ -> ((x = ∅)  /\ (y = ∅)).
Proof.
intros.
split.
apply eset_union_l in X; assumption.
rewrite comm in X.
apply eset_union_l in X. assumption.
Defined.



Lemma non_empty_union_l `{Funext} : 
	forall x y: FSet A,   x <> E -> x ∪ y <> E.
intros x y He.
intro Hu. 
apply He.
apply eq_subset in Hu.
destruct Hu as [_ H1].
apply union_subset in H1.
apply eset_subset_l.
destruct H1.
assumption.
Defined.

Lemma non_empty_union_r `{Funext} : 
	forall x y: FSet A,   y <> E -> x ∪ y <> E.
intros x y He.
intro Hu. 
apply He.
apply eq_subset in Hu.
destruct Hu as [_ H1].
apply union_subset in H1.
apply eset_subset_l.
destruct H1.
assumption.
Defined.



Theorem contrapositive : forall P Q : Type,
   (P -> Q) -> (not Q -> not P) .
Proof.
intros p q H1 H2.
unfold "~".
intro H3.
apply H1 in H3. apply H2 in H3. assumption.
Defined.



Lemma non_empty_singleton : forall a: A, L a <> E. 
intros a H.
enough (false = true).
 contradiction (false_ne_true X). 
transitivity (isIn a E).
cbn. reflexivity. 
transitivity (a ∈ (L a)).
apply (ap (fun x => a ∈ x) H^) .
cbn. destruct (dec (a = a)). 
reflexivity.
destruct n. 
reflexivity.
Defined.


(* Lemma aux `{Funext}: forall x: FSet A, forall p q: x = ∅  -> False,  p = q.
intros. apply path_forall. intro.
apply path_ishprop.
Defined.*)


Lemma fset_eset_dec `{Funext}: forall x: FSet A, x = ∅ \/ x <> ∅.
hinduction.
- left; reflexivity.
- right. apply non_empty_singleton.
- intros x y [G1 | G2] [G3 | G4].
	+ left. rewrite G1, G3. apply nl.
	+ right. apply non_empty_union_r; assumption.
	+ right. apply non_empty_union_l; assumption.
	+ right. apply non_empty_union_l; assumption.
- intros. destruct px, py, pz; apply path_sum; destruct_match_1.
	+   rewrite p, p0, p1.  rewrite nl. rewrite nl. reflexivity. 
	+ assumption.
	+ rewrite p, p0 in p1. rewrite nl in p1. rewrite comm in p1. rewrite nl in p1.
		assumption.
	+ rewrite p in p0. rewrite nl in p0. 	 
	  apply (non_empty_union_l y z) in n.  eq_neq_tac.
	+ rewrite p, p0 in p1. rewrite nr in p1. rewrite nr in p1. assumption.
	+ rewrite p in p0. rewrite nr in p0. 
		apply (non_empty_union_l x z) in n.  eq_neq_tac.
	+ rewrite p in p0. rewrite nr in p0. 
	 	apply (non_empty_union_l x y) in n.  eq_neq_tac.
	+ apply (non_empty_union_l x y) in n.
	  apply (non_empty_union_l (x ∪ y) z) in n. eq_neq_tac.
- intros. destruct px, py; apply path_sum; destruct_match_1.
	+ rewrite p, p0; apply union_idem.
	+ rewrite p in p0. rewrite nr in p0. assumption.
	+ rewrite p in p0. rewrite nl in p0. assumption.
	+ apply (non_empty_union_r y x) in n. eq_neq_tac.
- intros x px.
	destruct px. apply path_sum; destruct_match_1.
	+ assumption.
	+ apply path_sum; destruct_match_1. assumption.
- intros x px.
	destruct px. apply path_sum; destruct_match_1.
	+ assumption.
	+ apply path_sum; destruct_match_1. assumption.
- intros. cbn. apply path_sum. destruct_match_1.
  + apply (non_empty_singleton x). apply p.
Defined.




 
Lemma union_non_empty `{Funext}: 
  forall X1 X2: FSet A, U X1 X2 <> ∅ -> X1 <> ∅ \/ X2 <> ∅.
intros X1 X2 G. 
specialize (fset_eset_dec X1).
intro. destruct X. rewrite p in G. rewrite nl in G. 
right. assumption. left. apply n.
Defined.

Lemma union_non_empty' `{Funext}: 
  forall X1 X2: FSet A, U X1 X2 <> ∅ -> 
  	(X1 <> ∅ /\ X2 = ∅) \/ 
  	(X1 = ∅ /\ X2 <> ∅) \/
  	(X1 <> ∅ /\ X2 <> ∅ ).
intros X1 X2 G. 
specialize (fset_eset_dec X1).
specialize (fset_eset_dec X2).
intros H1 H2.
destruct H1, H2.
- rewrite p, p0 in G. destruct G. apply union_idem.
- left; split; assumption.
- right. left.  split; assumption.
- right. right. split; assumption.
Defined.



End  EmptySetProperties.
