Require Import HoTT.
Require Import HitTactics.
Require Import definition.
Require Import operations.
Require Import properties.
Require Import empty_set.
Class Antisymmetric {A} (R : relation A) :=
  antisymmetry : forall x y, R x y -> R y x -> x = y.
  
  
Class Total {A} (R : relation A) :=
  total : forall x y,  x = y \/ R x y \/ R y x. 
  
Class TotalOrder {A} (R : relation A) :=
  { TotalOrder_Reflexive : Reflexive R | 2 ;
    TotalOrder_Antisymmetric : Antisymmetric R | 2; 
    TotalOrder_Transitive : Transitive R | 2;
    TotalOrder_Total : Total R | 2; }. 

Context {A : Type0}.
Context {A_deceq : DecidablePaths A}.
Context {R: relation A}.
Context {A_ordered : TotalOrder R}.


Ltac eq_neq_tac :=
match goal  with
    |  [ H: ?x <> E, H': ?x = E |- _ ] => destruct H; assumption
end.


Ltac destruct_match_1 :=
	repeat match goal with
    | [|- match ?X with | _ => _ end ] => destruct X
    | [|- ?X = ?Y ] => apply path_ishprop
    | [ H: ?x <> E  |- Empty ] => destruct H
    | [  H1: ?x = E, H2: ?y = E, H3: ?w ∪ ?q  = E |- ?r = E]
    			=> rewrite H1, H2 in H3; rewrite nl in H3;  rewrite nl in H3
  end.
			

Lemma transport_dom_eq (D1 D2 C: Type) (P: D1 = D2) (f: D1 -> C) : 
transport (fun T: Type => T -> C) P f = fun y => f (transport (fun X => X) P^ y).
Proof.
induction P.
hott_simpl.
Defined.

Lemma transport_dom_eq_gen (Ty: Type) (D1 D2: Ty) (C: Type) (P: D1 = D2) 
			(Q : Ty -> Type) (f: Q D1 -> C) : 
transport (fun X: Ty => Q X -> C) P f = fun y => f (transport Q P^ y).
Proof.
induction P.
hott_simpl.
Defined.
			
Lemma min {HFun: Funext} (x: FSet A): x <> ∅  -> A.
Proof.
hrecursion x. 
- intro H. destruct H. reflexivity.
- intros. exact a.
- intros x y rx ry H.
	apply union_non_empty' in H.
	destruct H. 
	+ destruct p. specialize (rx fst). exact rx.
	+ destruct s. 
		* destruct p. specialize (ry snd). exact ry.
		* destruct p.  specialize (rx fst). specialize (ry snd).
			destruct (TotalOrder_Total rx ry) as [Heq | [ Hx | Hy ]].
			** exact rx.
			** exact rx.
			** exact ry.
- intros. rewrite transport_dom_eq_gen.
	apply path_forall. intro y0. 
	destruct (  union_non_empty' x y ∪ z 
	(transport (fun X : FSet A => X <> ∅) (assoc x y z)^ y0))
	as [[ G1 G2] | [[ G3 G4] | [G5 G6]]].
	+ pose (G2' := G2). apply  eset_union_lr in G2'; destruct G2'. cbn.
		destruct (union_non_empty' x ∪ y z y0) as 
	 [[H'x H'y] | [ [H'a H'b] | [H'c H'd]]]; try eq_neq_tac.
	 destruct (union_non_empty' x y H'x). 
	 	** destruct p. assert (G1 = fst0).  apply path_forall. intro.
		 apply path_ishprop. rewrite X. reflexivity. 
	 	** destruct s; destruct p; eq_neq_tac. 
	+ destruct (union_non_empty' y z G4)  as 
	[[H'x H'y] | [ [H'a H'b] | [H'c H'd]]]; try eq_neq_tac.
	destruct (union_non_empty' x ∪ y z y0).
		** destruct p. cbn. destruct (union_non_empty' x y fst).
			*** destruct p; eq_neq_tac.
			*** destruct s. destruct p.
				**** assert (H'x = snd0).  apply path_forall. intro.
		 apply path_ishprop. rewrite X. reflexivity.
		 	  **** destruct p. eq_neq_tac.
		** destruct s; destruct p; try eq_neq_tac.
		** destruct (union_non_empty' x ∪ y z y0).
			*** destruct p. eq_neq_tac.
			*** destruct s. destruct p.
				**** assert (H'b = snd).  apply path_forall. intro.
		 			apply path_ishprop. rewrite X. reflexivity.
		 		**** destruct p. assert (x ∪ y = E).
		 		rewrite H'a, G3. apply union_idem.  eq_neq_tac. 
		** cbn. destruct (TotalOrder_Total (py H'c) (pz H'd)).
			*** destruct (union_non_empty' x ∪ y z y0).
				**** destruct p0. eq_neq_tac.
				**** destruct s.
					*****  destruct p0. rewrite G3, nl in fst. eq_neq_tac.
					*****  destruct p0. destruct (union_non_empty' x y fst).
						****** destruct p0. eq_neq_tac.
						****** destruct s. 
						 ******* destruct p0. 
						 				destruct (TotalOrder_Total (py snd0) (pz snd)).
						 				f_ap. apply path_forall. intro.
		 								apply path_ishprop. 
		 								destruct s. f_ap. apply path_forall. intro.
		 								apply path_ishprop.
		 								rewrite p. f_ap. apply path_forall. intro.
		 								apply path_ishprop. 
		 				******* destruct p0. eq_neq_tac.
		 	*** destruct (union_non_empty' x ∪ y z y0).
		 		**** destruct p. eq_neq_tac.
		 		**** destruct s0. destruct p. rewrite comm in fst.
		 				 apply eset_union_l in fst. eq_neq_tac.
		 				 destruct p. 
		 				 destruct (union_non_empty' x y fst).
		 				 ***** destruct p; eq_neq_tac.
		 				 ***** destruct s0. destruct p. 
		 				 		destruct (TotalOrder_Total (py snd0) (pz snd));
		 				 		destruct s; try (f_ap;  apply path_forall; intro;
		 														 apply path_ishprop).
		 						rewrite p. f_ap;  apply path_forall; intro;
		 														 apply path_ishprop.
		 						destruct s0. 		f_ap;  apply path_forall; intro;
		 														 apply path_ishprop.
		 						assert (snd0 = H'c).   apply path_forall; intro;
		 														 apply path_ishprop.
		 						assert (snd = H'd).   apply path_forall; intro;
		 														 apply path_ishprop.
		 						rewrite <- X0 in r. rewrite X in r0.
		 						apply TotalOrder_Antisymmetric; assumption.
		 						destruct s0.				
		 						assert (snd0 = H'c).   apply path_forall; intro;
		 														 apply path_ishprop.
		 						assert (snd = H'd).   apply path_forall; intro;
		 														 apply path_ishprop.
		 						rewrite <- X in r. rewrite X0 in r0.
		 						apply TotalOrder_Antisymmetric; assumption.
		 						f_ap;  apply path_forall; intro;
		 														 apply path_ishprop.
		 						destruct p; eq_neq_tac.
	+ cbn. destruct (union_non_empty' y z G6).
		** destruct p. destruct ( union_non_empty' x ∪ y z y0).
			*** destruct p. destruct (union_non_empty' x y fst0).
				**** destruct p; eq_neq_tac.
				**** destruct s; destruct p. eq_neq_tac.		
						assert (fst1 = G5).   apply path_forall; intro;
		 														 apply path_ishprop.
		 				assert (fst = snd1).   apply path_forall; intro;
		 														 apply path_ishprop.
		 				rewrite X, X0.			
		 			  destruct (TotalOrder_Total (px G5) (py snd1)).
		 			  reflexivity.
		 			  destruct s; reflexivity.
		 	*** destruct s; destruct p; eq_neq_tac. 
		** destruct (union_non_empty' x ∪ y z y0). 
			*** destruct p. destruct s; destruct p; eq_neq_tac.
			*** destruct s. destruct p. destruct s0. destruct p.
					apply eset_union_l in fst0. eq_neq_tac.
				**** destruct p. 		
		 					assert (snd = snd0).   apply path_forall; intro;
		 														 apply path_ishprop.		 
				
				destruct (union_non_empty' x y fst0). 
				destruct p.
				 assert (fst1 = G5).  apply path_forall; intro;
		 														 apply path_ishprop. 
		 				assert (fst = snd1).  apply set_path2.
					***** rewrite X0. rewrite <- X. reflexivity.
					*****  destruct s; destruct p; eq_neq_tac.
				**** destruct s0. destruct p0. destruct p. 
					***** apply eset_union_l in fst. eq_neq_tac.
					***** destruct p, p0.
					assert (snd0 = snd).   apply path_forall; intro;
		 														 apply path_ishprop.
		 			rewrite X.												
					 destruct (union_non_empty' x y fst0).
					 destruct p; eq_neq_tac.
					 destruct s. destruct p; eq_neq_tac.
					 destruct p.
					 assert (fst = snd1).   apply path_forall; intro;
		 														 apply path_ishprop.
						assert (fst1 = G5).   apply path_forall; intro;
		 														 apply path_ishprop.								 
						rewrite <- X0. rewrite X1. 											
					  destruct (TotalOrder_Total (py fst) (pz snd)).
					  ****** rewrite <- p. 
					   destruct (TotalOrder_Total (px G5) (py fst)).
					   rewrite <- p0. 
					 		destruct (TotalOrder_Total (px G5) (px G5)).
					 		reflexivity.
					 		destruct s; reflexivity.
					 		destruct s. destruct (TotalOrder_Total (px G5) (py fst)).
					 		reflexivity.
					 		destruct s.
					 		reflexivity.
					 		apply TotalOrder_Antisymmetric; assumption.
					 		destruct (TotalOrder_Total (py fst) (py fst)).
					 		reflexivity.
					 		destruct s;
					 		reflexivity.
					 ****** destruct s. 
					 	destruct (TotalOrder_Total (px G5) (py fst)).
					 	destruct (TotalOrder_Total (px G5) (pz snd)).
					 	reflexivity.
					 	destruct s.
					 	reflexivity. rewrite <- p in r. 
					 	apply TotalOrder_Antisymmetric; assumption.
					 	destruct s. 
					 	destruct ( TotalOrder_Total (px G5) (pz snd)).
					 	reflexivity.
					 	destruct s. reflexivity.
					 	apply (TotalOrder_Transitive (px G5)) in r. 
					 	apply TotalOrder_Antisymmetric; assumption.
					 	assumption.
					 	destruct (TotalOrder_Total (py fst) (pz snd)). reflexivity.
					 	destruct s. reflexivity.
					 	apply TotalOrder_Antisymmetric; assumption.
					 *******
					 	 	destruct ( TotalOrder_Total (px G5) (py fst)).
					 	 	reflexivity.
					 	 	destruct s. destruct (TotalOrder_Total (px G5) (pz snd)).
					 	 	reflexivity. destruct s; reflexivity.
					 	 	destruct ( TotalOrder_Total (px G5) (pz snd)).
					 	 	rewrite <- p.
					 	 	destruct (TotalOrder_Total (py fst) (px G5)).
					 	 	apply symmetry; assumption.
					 	 	destruct s. rewrite <- p in r.
					 	 	apply TotalOrder_Antisymmetric; assumption.
					 	 	reflexivity. destruct s. 
					 	 	assert ((py fst) = (pz snd)). apply TotalOrder_Antisymmetric.
					 	 	apply (TotalOrder_Transitive (py fst) (px G5)); assumption.
					 	 	assumption. rewrite X2. assert (px G5 = pz snd).
					 	 	 apply TotalOrder_Antisymmetric. assumption.
					 	 	 apply (TotalOrder_Transitive (pz snd) (py fst)); assumption.
					 	 	 rewrite X3.
					 	 	destruct ( TotalOrder_Total (pz snd) (pz snd)).
					 	 	reflexivity. destruct s; reflexivity.
					 	 	destruct (TotalOrder_Total (py fst) (pz snd)).
					 	 		 apply TotalOrder_Antisymmetric.  assumption. rewrite p.
					 	 	 apply (TotalOrder_Reflexive).  destruct s. 
					 	 		 apply TotalOrder_Antisymmetric;  assumption. reflexivity.
- intros. rewrite transport_dom_eq_gen.
  apply path_forall. intro y0. cbn.
   destruct 
  		(union_non_empty' x y 
  		(transport (fun X : FSet A => X <> ∅) (comm x y)^ y0)) as 
  		[[Hx Hy] | [ [Ha Hb] | [Hc Hd]]];
  	destruct (union_non_empty' y x y0) as 
  	   [[H'x H'y] | [ [H'a H'b] | [H'c H'd]]];
  	   try (eq_neq_tac). 
     assert (Hx = H'b).  apply path_forall. intro.
		 apply path_ishprop. rewrite X. reflexivity.
		 assert (Hb = H'x).  apply path_forall. intro.
		 apply path_ishprop. rewrite X. reflexivity.
		  assert (Hd = H'c).  apply path_forall. intro.
		 apply path_ishprop. rewrite X.
		  assert (H'd = Hc).  apply path_forall. intro.
		 apply path_ishprop.
		 rewrite X0. rewrite <- X.
	destruct 
		(TotalOrder_Total (px Hc) (py Hd)) as [G1 | [G2 | G3]];
	destruct 
	(TotalOrder_Total (py Hd) (px Hc)) as [T1 | [T2 | T3]];
	try (assumption);
	try (reflexivity);
	try (apply symmetry; assumption);
	try (apply TotalOrder_Antisymmetric; assumption).
		 		  
- intros. rewrite transport_dom_eq_gen.
  apply path_forall. intro y.
  destruct (union_non_empty' ∅ x (transport (fun X : FSet A => X <> ∅) (nl x)^ y)).
  destruct p. eq_neq_tac. 
  destruct s. 
  destruct p.
  assert (y = snd).
    apply path_forall. intro.
    apply path_ishprop. rewrite X. reflexivity.
  destruct p. destruct fst.
- intros. rewrite transport_dom_eq_gen.
  apply path_forall. intro y.
  destruct (union_non_empty' x ∅ (transport (fun X : FSet A => X <> ∅) (nr x)^ y)).
  destruct p. assert (y = fst).  apply path_forall. intro.
apply path_ishprop. rewrite X. reflexivity.
  destruct s. 
  destruct p. 
  eq_neq_tac.
  destruct p.
  destruct snd.
- intros. rewrite transport_dom_eq_gen.
	apply path_forall. intro y. 
  destruct ( union_non_empty' {|x|} {|x|} (transport (fun X : FSet A => X <> ∅) (idem x)^ y)).
  reflexivity.
  destruct s.
  reflexivity.
  destruct p.
  cbn. destruct  (TotalOrder_Total x x). reflexivity.
  destruct s; reflexivity.
Defined.
	

Definition minfset {HFun: Funext} : 
	FSet A -> { Y: (FSet A) & (Y = E) + { a: A & Y = L a } }.
intro X.
hinduction X.
-  exists E. left. reflexivity.
- intro a.  exists (L a). right. exists a. reflexivity.
- intros IH1 IH2.
  destruct IH1 as [R1 HR1].
  destruct IH2 as [R2 HR2]. 
  destruct HR1. 
  destruct HR2.
  exists E; left. reflexivity.
  destruct s as [a Ha]. exists (L a). right.
  exists a. reflexivity.
  destruct HR2. 
  destruct s as [a Ha].
  exists (L a). right. exists a. reflexivity.
  destruct s as [a1 Ha1].
  destruct s0 as [a2 Ha2].
  assert (a1 = a2 \/ R a1 a2 \/ R a2 a1).
	apply TotalOrder_Total. 
	destruct X.
	exists (L a1). right. exists a1. reflexivity.
	destruct s.
	exists (L a1). right. exists a1. reflexivity.
  exists (L a2). right. exists a2. reflexivity.
  - cbn. intros R1 R2 R3.
  destruct R1 as [Res1 HR1].
  destruct HR1 as [HR1E | HR1S].
  destruct R2 as [Res2 HR2].
  destruct HR2 as [HR2E | HR2S].
  destruct R3 as [Res3 HR3].
  destruct HR3 as [HR3E | HR3S].
  + cbn. reflexivity.
 	+ cbn. reflexivity.
 	+ cbn.   destruct R3 as [Res3 HR3].
  destruct HR3 as [HR3E | HR3S].
  * cbn. reflexivity.
  * destruct HR2S as [a2 Ha2].  
    destruct HR3S as [a3 Ha3].
  	  destruct (TotalOrder_Total a2 a3).
  	  ** cbn. reflexivity.
  	  ** destruct s. cbn. reflexivity.
  	  	   cbn. reflexivity.  	
  	+  destruct HR1S as [a1 Ha1].
  	 destruct R2 as [Res2 HR2].
  destruct HR2 as [HR2E | HR2S].
  destruct R3 as [Res3 HR3].
  destruct HR3 as [HR3E | HR3S].
  * cbn. reflexivity.
  * destruct HR3S as [a3 Ha3].
    destruct (TotalOrder_Total a1 a3). 
    reflexivity.
    destruct s; reflexivity.
   * destruct HR2S as [a2 Ha2]. 
  destruct R3 as [Res3 HR3].
  destruct HR3 as [HR3E | HR3S].
    cbn. destruct (TotalOrder_Total a1 a2).
    cbn. reflexivity.
    destruct s.
    cbn. reflexivity.
    cbn. reflexivity.
    destruct HR3S as [a3 Ha3]. 
     destruct (TotalOrder_Total a2 a3).
     ** rewrite p. 
     destruct (TotalOrder_Total a1 a3).
     rewrite p0. 
     destruct ( TotalOrder_Total a3 a3).
     reflexivity.
     destruct s; reflexivity.
     destruct s. cbn.
     destruct (TotalOrder_Total a1 a3).
     reflexivity.
     destruct s. reflexivity.
     	assert (a1 = a3).
	  apply TotalOrder_Antisymmetric; assumption. 
	  rewrite X. reflexivity.
	  cbn. destruct (TotalOrder_Total a3 a3).
	  reflexivity.
	  destruct s; reflexivity.
    ** destruct s.
    		 *** cbn. destruct (TotalOrder_Total a1 a2).
    		 cbn. destruct (TotalOrder_Total a1 a3).
    		  reflexivity.
    		  destruct s. reflexivity.
    		  rewrite <- p in r.
    		    	assert (a1 = a3).
	  apply TotalOrder_Antisymmetric; assumption. 
	  rewrite X. reflexivity.
	    destruct s. cbn.
    	destruct (TotalOrder_Total a1 a3).
    	reflexivity.
    	destruct s. reflexivity.
    	assert (R a1 a3).
    apply (TotalOrder_Transitive a1 a2); assumption.
    assert (a1 = a3).
	  apply TotalOrder_Antisymmetric; assumption. 
	  rewrite X0. reflexivity.
    	cbn. destruct (TotalOrder_Total a2 a3).
    	reflexivity.
    	destruct s.
    	reflexivity.
    assert (a2 = a3).
	  apply TotalOrder_Antisymmetric; assumption. 
	  rewrite X. reflexivity.
   *** cbn. destruct (TotalOrder_Total a1 a3).
   rewrite p. destruct (TotalOrder_Total a3 a2).
   cbn. destruct (TotalOrder_Total a3 a3).
   reflexivity. destruct s; reflexivity.
   destruct s. cbn.
   destruct (TotalOrder_Total a3 a3).
   reflexivity. destruct s; reflexivity.
   cbn. destruct (TotalOrder_Total a2 a3).
   rewrite p0.
   reflexivity.
   destruct s. 
    assert (a2 = a3).
	  apply TotalOrder_Antisymmetric; assumption. 
	  rewrite X. reflexivity. reflexivity.
	  destruct s.
	  cbn.
    destruct (TotalOrder_Total a1 a2).
    cbn. 
  destruct (TotalOrder_Total a1 a3).
  reflexivity.
  assert (a1 = a3).
  apply TotalOrder_Antisymmetric. assumption.
  rewrite <- p in r. assumption.
  destruct s. reflexivity. rewrite X. reflexivity.
  destruct s. cbn. 
  destruct (TotalOrder_Total a1 a3). reflexivity.
  destruct s. reflexivity.
  assert (a1 = a3).
  apply TotalOrder_Antisymmetric; assumption.
  rewrite X. reflexivity.
  cbn.  destruct  (TotalOrder_Total a2 a3).
  rewrite p in r1.
  assert (a2 = a1).
  transitivity a3.
  assumption.
  apply TotalOrder_Antisymmetric; assumption.
  rewrite X. reflexivity.
  destruct s. 
   assert (a1 = a2).
    apply TotalOrder_Antisymmetric.
   apply (TotalOrder_Transitive a1 a3); assumption.
   assumption.
  rewrite X. reflexivity.
   assert (a1 = a3).
    apply TotalOrder_Antisymmetric.
    assumption.
   apply (TotalOrder_Transitive a3 a2); assumption.
   rewrite X. reflexivity.
  destruct ( TotalOrder_Total a1 a2).
  cbn.
  destruct (TotalOrder_Total a1 a3).
  rewrite p0.
  reflexivity.
  destruct s. 
  assert (a1 = a3).
    apply TotalOrder_Antisymmetric; assumption. 
    rewrite X. reflexivity. reflexivity. 
  destruct s.
  cbn.
  destruct (TotalOrder_Total a1 a3 ).
  rewrite p.
  reflexivity.
  destruct s. 
    assert (a1 = a3).
    apply TotalOrder_Antisymmetric; assumption. 
    rewrite X. reflexivity. reflexivity. 
  cbn.
  destruct (TotalOrder_Total a1 a3 ).
  assert (a2 = a3).
  rewrite p in r1.
  apply TotalOrder_Antisymmetric; assumption. 
	  rewrite X. destruct (TotalOrder_Total a3 a3). reflexivity.
	  destruct s; reflexivity.
  destruct s. 
  destruct (TotalOrder_Total a2 a3).
  rewrite p.
  reflexivity.
  destruct s.
    assert (a2 = a3).
	  apply TotalOrder_Antisymmetric; assumption. 
	  rewrite X. reflexivity.
	  reflexivity.
   	cbn. destruct (TotalOrder_Total a2 a3).
   	rewrite p.
    	reflexivity.
    	destruct s.
    	assert (a2 = a3).
    	  apply TotalOrder_Antisymmetric; assumption.
    	  rewrite X. reflexivity. reflexivity.
  - cbn. intros R1 R2. 
  destruct R1 as [La1 HR1].
  destruct HR1 as [HR1E | HR1S]. 
  destruct R2 as [La2 HR2].
  destruct HR2 as [HR2E | HR2S].
  reflexivity.
  reflexivity.
  destruct R2 as [La2 HR2].
  destruct HR2 as [HR2E | HR2S].
  reflexivity.
  destruct HR1S as [a1 Ha1].
  destruct HR2S as [a2 Ha2].
  destruct (TotalOrder_Total a1 a2).
  rewrite p.
  destruct (TotalOrder_Total a2 a2).
  reflexivity.
  destruct s; reflexivity.
	destruct s.
	destruct (TotalOrder_Total a2 a1).
	rewrite p.
	reflexivity.
	destruct s.
	assert (a1 = a2).
	apply TotalOrder_Antisymmetric; assumption.
	rewrite X.
	reflexivity.
	reflexivity.
	destruct (TotalOrder_Total a2 a1).
	rewrite p.
	reflexivity.
	destruct s.
	reflexivity.
		assert (a1 = a2).
	apply TotalOrder_Antisymmetric; assumption.
	rewrite X.
	reflexivity.
  - cbn. intro R. destruct R as [La HR].
  destruct HR. rewrite <- p. reflexivity.
  destruct s as [a1 H].
  apply (path_sigma' _  H^).
  rewrite transport_sum.
  f_ap.
  rewrite transport_sigma.
  simpl.
  simple refine (path_sigma' _ _ _ ).
  apply transport_const.
  apply set_path2.

  - intros R. cbn. 
  destruct R as [ R  HR].
  destruct HR as [HE | Ha ].
  rewrite <- HE. reflexivity.
  destruct Ha as [a Ha].
  apply (path_sigma' _  Ha^).
  rewrite transport_sum.
  f_ap.
  rewrite transport_sigma.
  simpl.
  simple refine (path_sigma' _ _ _ ).
  apply transport_const.
  apply set_path2.
  - cbn. intro. 
  destruct (TotalOrder_Total x x).
  reflexivity.
  destruct s.
  reflexivity.
  reflexivity.
Defined.



