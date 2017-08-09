Require Import HoTT.
Require Import HitTactics.
Require Import definition.
Require Import operations.
Require Import properties.

Definition relation A := A -> A -> Type.

Section TotalOrder.
  Class IsTop (A : Type) (R : relation A) (a : A) :=
    top_max : forall x, R x a.
  
  Class LessThan (A : Type) :=
    leq : relation A.
  
  Class Antisymmetric {A} (R : relation A) :=
    antisymmetry : forall x y, R x y -> R y x -> x = y.
  
  Class Total {A} (R : relation A) :=
    total : forall x y,  x = y \/ R x y \/ R y x. 
  
  Class TotalOrder (A : Type) {R : LessThan A} :=
    { TotalOrder_Reflexive :> Reflexive R | 2 ;
      TotalOrder_Antisymmetric :> Antisymmetric R | 2; 
      TotalOrder_Transitive :> Transitive R | 2;
      TotalOrder_Total :> Total R | 2; }.
End TotalOrder.

Section minimum.
  Context {A : Type}.
  Context `{TotalOrder A}.

  Definition min (x y : A) : A.
  Proof.
    destruct (@total _ R _ x y).
    - apply x.
    - destruct s as [s | s].
      * apply x.
      * apply y.
  Defined.

  Lemma min_spec1 x y : R (min x y) x.
  Proof.
    unfold min.
    destruct (total x y) ; simpl.
    - reflexivity.
    - destruct s as [ | t].
      * reflexivity.
      * apply t.
  Defined.

  Lemma min_spec2 x y z : R z x -> R z y -> R z (min x y).
  Proof.
    intros.
    unfold min.
    destruct (total x y) as [ | s].
    * assumption.
    * try (destruct s) ; assumption.
  Defined.
  
  Lemma min_comm x y : min x y = min y x.
  Proof.
    unfold min.
    destruct (total x y) ; destruct (total y x) ; simpl.
    - assumption.
    - destruct s as [s | s] ; auto.
    - destruct s as [s | s] ; symmetry ; auto.
    - destruct s as [s | s] ; destruct s0 as [s0 | s0] ; try reflexivity.
      * apply (@antisymmetry _ R _ _) ; assumption.
      * apply (@antisymmetry _ R _ _) ; assumption.
  Defined.

  Lemma min_idem x : min x x = x.
  Proof.
    unfold min.
    destruct (total x x) ; simpl.
    - reflexivity.
    - destruct s ; reflexivity.
  Defined.

  Lemma min_assoc x y z : min (min x y) z = min x (min y z).
  Proof.
    apply (@antisymmetry _ R _ _).
    - apply min_spec2.
      * etransitivity ; apply min_spec1.
      * apply min_spec2.
        ** etransitivity ; try (apply min_spec1).
           simpl.
           rewrite min_comm ; apply min_spec1.
        ** rewrite min_comm ; apply min_spec1.
    - apply min_spec2.
      * apply min_spec2.
        ** apply min_spec1.
        ** etransitivity.
           { rewrite min_comm ; apply min_spec1. }
           apply min_spec1.
      * transitivity (min y z); simpl
        ; rewrite min_comm ; apply min_spec1.
  Defined.
  
  Variable (top : A).
  Context `{IsTop A R top}.

  Lemma min_nr x : min x top = x.
  Proof.
    intros.
    unfold min.
    destruct (total x top).
    - reflexivity.
    - destruct s.
      * reflexivity.
      * apply (@antisymmetry _ R _ _).
        ** assumption.
        ** refine (top_max _). apply _.
  Defined.

  Lemma min_nl x : min top x = x.
  Proof.
    rewrite min_comm.
    apply min_nr.
  Defined.

  Lemma min_top_l x y : min x y = top -> x = top.
  Proof.
    unfold min.
    destruct (total x y).
    - apply idmap.
    - destruct s as [s | s].
      * apply idmap.
      * intros X.
        rewrite X in s.
        apply (@antisymmetry _ R _ _).
        ** apply top_max.
        ** assumption.
  Defined.
  
  Lemma min_top_r x y : min x y = top -> y = top.
  Proof.
    rewrite min_comm.
    apply min_top_l.
  Defined.

End minimum.

Section add_top.
  Variable (A : Type).
  Context `{TotalOrder A}.

  Definition Top := A + Unit.
  Definition top : Top := inr tt.

  Global Instance RTop : LessThan Top.
  Proof.
    unfold relation.
    induction 1 as [a1 | ] ; induction 1 as [a2 | ].
    - apply (R a1 a2).
    - apply Unit_hp.
    - apply False_hp.
    - apply Unit_hp.
  Defined.

  Global Instance rtop_hprop :
    is_mere_relation A R -> is_mere_relation Top RTop.
  Proof.
    intros P a b.
    destruct a ; destruct b ; apply _.
  Defined.
  
  Global Instance RTopOrder : TotalOrder Top.
  Proof.
    split.
    - intros x ; induction x ; unfold RTop ; simpl.
      * reflexivity.
      * apply tt.
    - intros x y ; induction x as [a1 | ] ; induction y as [a2 | ] ; unfold RTop ; simpl
      ; try contradiction.
      * intros ; f_ap.
        apply (@antisymmetry _ R _ _) ; assumption.
      * intros ; induction b ; induction b0.
        reflexivity.
    - intros x y z ; induction x as [a1 | b1] ; induction y as [a2 | b2]
      ; induction z as [a3 | b3] ; unfold RTop ; simpl
      ; try contradiction ; intros ; try (apply tt).
      transitivity a2 ; assumption.
    - intros x y.
      unfold RTop ; simpl.
      induction x as [a1 | b1] ; induction y as [a2 | b2] ; try (apply (inl idpath)).
      * destruct (TotalOrder_Total a1 a2).
        ** left ; f_ap ; assumption.
        ** right ; assumption.
      * apply (inr(inl tt)).
      * apply (inr(inr tt)).
      * left ; induction b1 ; induction b2 ; reflexivity.
  Defined.

  Global Instance top_a_top : IsTop Top RTop top.
  Proof.
    intro x ; destruct x ; apply tt.
  Defined.
End add_top.  

Section min_set.
  Variable (A : Type).
  Context `{TotalOrder A}.
  Context `{is_mere_relation A R}.
  Context `{Univalence} `{IsHSet A}.

  Definition min_set : FSet A -> Top A.
  Proof.
    hrecursion.
    - apply (top A).
    - apply inl.
    - apply min.
    - intros ; symmetry ; apply min_assoc.
    - apply min_comm.
    - apply min_nl. apply _.
    - apply min_nr. apply _.
    - intros ; apply min_idem.
  Defined.

  Definition empty_min : forall (X : FSet A), min_set X = top A -> X = ∅.
  Proof.
    simple refine (FSet_ind _ _ _ _ _ _ _ _ _ _ _)
    ; try (intros ; apply path_forall ; intro q ; apply set_path2)
    ; simpl.
    - intros ; reflexivity.
    - intros.
      unfold top in X.
      enough Empty.
      { contradiction. }
      refine (not_is_inl_and_inr' (inl a) _ _).
      * apply tt.
      * rewrite X ; apply tt.
    - intros.
      assert (min_set x = top A).
      {
        simple refine (min_top_l _ _ (min_set y) _) ; assumption.
      }
      rewrite (X X2).
      rewrite nl.
      assert (min_set y = top A).
      { simple refine (min_top_r _ (min_set x) _ _) ; assumption. }
      rewrite (X0 X3).
      reflexivity.
  Defined.
  
  Definition min_set_spec (a : A) : forall (X : FSet A),
      a ∈ X -> RTop A (min_set X) (inl a).
  Proof.
    simple refine (FSet_ind _ _ _ _ _ _ _ _ _ _ _)
    ; try (intros ; apply path_ishprop)
    ; simpl.    
    - contradiction.
    - intros.
      strip_truncations.
      rewrite X.
      reflexivity.
    - intros.
      strip_truncations.
      unfold member in X, X0.
      destruct X1.
      * specialize (X t).
        assert (RTop A (min (min_set x) (min_set y)) (min_set x)) as X1.
        { apply min_spec1. }
        etransitivity.
        { apply X1. }
        assumption.
      * specialize (X0 t).
        assert (RTop A (min (min_set x) (min_set y)) (min_set y)) as X1.
        { rewrite min_comm ; apply min_spec1. }
        etransitivity.
        { apply X1. }
        assumption.
  Defined.

End min_set.


(*
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
			
(* Lemma min {HFun: Funext} (x: FSet A): x <> ∅  -> A. *)
(* Proof. *)
(* hrecursion x.  *)
(* - intro H. destruct H. reflexivity. *)
(* - intros. exact a. *)
(* - intros x y rx ry H. *)
(* 	apply union_non_empty' in H. *)
(* 	destruct H.  *)
(* 	+ destruct p. specialize (rx fst). exact rx. *)
(* 	+ destruct s.  *)
(* 		* destruct p. specialize (ry snd). exact ry. *)
(* 		* destruct p.  specialize (rx fst). specialize (ry snd). *)
(* 			destruct (TotalOrder_Total rx ry) as [Heq | [ Hx | Hy ]]. *)
(* 			** exact rx. *)
(* 			** exact rx. *)
(* 			** exact ry. *)
(* - intros. rewrite transport_dom_eq_gen. *)
(* 	apply path_forall. intro y0.  *)
(* 	destruct (  union_non_empty' x y ∪ z  *)
(* 	(transport (fun X : FSet A => X <> ∅) (assoc x y z)^ y0)) *)
(* 	as [[ G1 G2] | [[ G3 G4] | [G5 G6]]]. *)
(* 	+ pose (G2' := G2). apply  eset_union_lr in G2'; destruct G2'. cbn. *)
(* 		destruct (union_non_empty' x ∪ y z y0) as  *)
(* 	 [[H'x H'y] | [ [H'a H'b] | [H'c H'd]]]; try eq_neq_tac. *)
(* 	 destruct (union_non_empty' x y H'x).  *)
(* 	 	** destruct p. assert (G1 = fst0).  apply path_forall. intro. *)
(* 		 apply path_ishprop. rewrite X. reflexivity.  *)
(* 	 	** destruct s; destruct p; eq_neq_tac.  *)
(* 	+ destruct (union_non_empty' y z G4)  as  *)
(* 	[[H'x H'y] | [ [H'a H'b] | [H'c H'd]]]; try eq_neq_tac. *)
(* 	destruct (union_non_empty' x ∪ y z y0). *)
(* 		** destruct p. cbn. destruct (union_non_empty' x y fst). *)
(* 			*** destruct p; eq_neq_tac. *)
(* 			*** destruct s. destruct p. *)
(* 				**** assert (H'x = snd0).  apply path_forall. intro. *)
(* 		 apply path_ishprop. rewrite X. reflexivity. *)
(* 		 	  **** destruct p. eq_neq_tac. *)
(* 		** destruct s; destruct p; try eq_neq_tac. *)
(* 		** destruct (union_non_empty' x ∪ y z y0). *)
(* 			*** destruct p. eq_neq_tac. *)
(* 			*** destruct s. destruct p. *)
(* 				**** assert (H'b = snd).  apply path_forall. intro. *)
(* 		 			apply path_ishprop. rewrite X. reflexivity. *)
(* 		 		**** destruct p. assert (x ∪ y = E). *)
(* 		 		rewrite H'a, G3. apply union_idem.  eq_neq_tac.  *)
(* 		** cbn. destruct (TotalOrder_Total (py H'c) (pz H'd)). *)
(* 			*** destruct (union_non_empty' x ∪ y z y0). *)
(* 				**** destruct p0. eq_neq_tac. *)
(* 				**** destruct s. *)
(* 					*****  destruct p0. rewrite G3, nl in fst. eq_neq_tac. *)
(* 					*****  destruct p0. destruct (union_non_empty' x y fst). *)
(* 						****** destruct p0. eq_neq_tac. *)
(* 						****** destruct s.  *)
(* 						 ******* destruct p0.  *)
(* 						 				destruct (TotalOrder_Total (py snd0) (pz snd)). *)
(* 						 				f_ap. apply path_forall. intro. *)
(* 		 								apply path_ishprop.  *)
(* 		 								destruct s. f_ap. apply path_forall. intro. *)
(* 		 								apply path_ishprop. *)
(* 		 								rewrite p. f_ap. apply path_forall. intro. *)
(* 		 								apply path_ishprop.  *)
(* 		 				******* destruct p0. eq_neq_tac. *)
(* 		 	*** destruct (union_non_empty' x ∪ y z y0). *)
(* 		 		**** destruct p. eq_neq_tac. *)
(* 		 		**** destruct s0. destruct p. rewrite comm in fst. *)
(* 		 				 apply eset_union_l in fst. eq_neq_tac. *)
(* 		 				 destruct p.  *)
(* 		 				 destruct (union_non_empty' x y fst). *)
(* 		 				 ***** destruct p; eq_neq_tac. *)
(* 		 				 ***** destruct s0. destruct p.  *)
(* 		 				 		destruct (TotalOrder_Total (py snd0) (pz snd)); *)
(* 		 				 		destruct s; try (f_ap;  apply path_forall; intro; *)
(* 		 														 apply path_ishprop). *)
(* 		 						rewrite p. f_ap;  apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 		 						destruct s0. 		f_ap;  apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 		 						assert (snd0 = H'c).   apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 		 						assert (snd = H'd).   apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 		 						rewrite <- X0 in r. rewrite X in r0. *)
(* 		 						apply TotalOrder_Antisymmetric; assumption. *)
(* 		 						destruct s0.				 *)
(* 		 						assert (snd0 = H'c).   apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 		 						assert (snd = H'd).   apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 		 						rewrite <- X in r. rewrite X0 in r0. *)
(* 		 						apply TotalOrder_Antisymmetric; assumption. *)
(* 		 						f_ap;  apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 		 						destruct p; eq_neq_tac. *)
(* 	+ cbn. destruct (union_non_empty' y z G6). *)
(* 		** destruct p. destruct ( union_non_empty' x ∪ y z y0). *)
(* 			*** destruct p. destruct (union_non_empty' x y fst0). *)
(* 				**** destruct p; eq_neq_tac. *)
(* 				**** destruct s; destruct p. eq_neq_tac.		 *)
(* 						assert (fst1 = G5).   apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 		 				assert (fst = snd1).   apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 		 				rewrite X, X0.			 *)
(* 		 			  destruct (TotalOrder_Total (px G5) (py snd1)). *)
(* 		 			  reflexivity. *)
(* 		 			  destruct s; reflexivity. *)
(* 		 	*** destruct s; destruct p; eq_neq_tac.  *)
(* 		** destruct (union_non_empty' x ∪ y z y0).  *)
(* 			*** destruct p. destruct s; destruct p; eq_neq_tac. *)
(* 			*** destruct s. destruct p. destruct s0. destruct p. *)
(* 					apply eset_union_l in fst0. eq_neq_tac. *)
(* 				**** destruct p. 		 *)
(* 		 					assert (snd = snd0).   apply path_forall; intro; *)
(* 		 														 apply path_ishprop.		  *)
				
(* 				destruct (union_non_empty' x y fst0).  *)
(* 				destruct p. *)
(* 				 assert (fst1 = G5).  apply path_forall; intro; *)
(* 		 														 apply path_ishprop.  *)
(* 		 				assert (fst = snd1).  apply set_path2. *)
(* 					***** rewrite X0. rewrite <- X. reflexivity. *)
(* 					*****  destruct s; destruct p; eq_neq_tac. *)
(* 				**** destruct s0. destruct p0. destruct p.  *)
(* 					***** apply eset_union_l in fst. eq_neq_tac. *)
(* 					***** destruct p, p0. *)
(* 					assert (snd0 = snd).   apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 		 			rewrite X.												 *)
(* 					 destruct (union_non_empty' x y fst0). *)
(* 					 destruct p; eq_neq_tac. *)
(* 					 destruct s. destruct p; eq_neq_tac. *)
(* 					 destruct p. *)
(* 					 assert (fst = snd1).   apply path_forall; intro; *)
(* 		 														 apply path_ishprop. *)
(* 						assert (fst1 = G5).   apply path_forall; intro; *)
(* 		 														 apply path_ishprop.								  *)
(* 						rewrite <- X0. rewrite X1. 											 *)
(* 					  destruct (TotalOrder_Total (py fst) (pz snd)). *)
(* 					  ****** rewrite <- p.  *)
(* 					   destruct (TotalOrder_Total (px G5) (py fst)). *)
(* 					   rewrite <- p0.  *)
(* 					 		destruct (TotalOrder_Total (px G5) (px G5)). *)
(* 					 		reflexivity. *)
(* 					 		destruct s; reflexivity. *)
(* 					 		destruct s. destruct (TotalOrder_Total (px G5) (py fst)). *)
(* 					 		reflexivity. *)
(* 					 		destruct s. *)
(* 					 		reflexivity. *)
(* 					 		apply TotalOrder_Antisymmetric; assumption. *)
(* 					 		destruct (TotalOrder_Total (py fst) (py fst)). *)
(* 					 		reflexivity. *)
(* 					 		destruct s; *)
(* 					 		reflexivity. *)
(* 					 ****** destruct s.  *)
(* 					 	destruct (TotalOrder_Total (px G5) (py fst)). *)
(* 					 	destruct (TotalOrder_Total (px G5) (pz snd)). *)
(* 					 	reflexivity. *)
(* 					 	destruct s. *)
(* 					 	reflexivity. rewrite <- p in r.  *)
(* 					 	apply TotalOrder_Antisymmetric; assumption. *)
(* 					 	destruct s.  *)
(* 					 	destruct ( TotalOrder_Total (px G5) (pz snd)). *)
(* 					 	reflexivity. *)
(* 					 	destruct s. reflexivity. *)
(* 					 	apply (TotalOrder_Transitive (px G5)) in r.  *)
(* 					 	apply TotalOrder_Antisymmetric; assumption. *)
(* 					 	assumption. *)
(* 					 	destruct (TotalOrder_Total (py fst) (pz snd)). reflexivity. *)
(* 					 	destruct s. reflexivity. *)
(* 					 	apply TotalOrder_Antisymmetric; assumption. *)
(* 					 ******* *)
(* 					 	 	destruct ( TotalOrder_Total (px G5) (py fst)). *)
(* 					 	 	reflexivity. *)
(* 					 	 	destruct s. destruct (TotalOrder_Total (px G5) (pz snd)). *)
(* 					 	 	reflexivity. destruct s; reflexivity. *)
(* 					 	 	destruct ( TotalOrder_Total (px G5) (pz snd)). *)
(* 					 	 	rewrite <- p. *)
(* 					 	 	destruct (TotalOrder_Total (py fst) (px G5)). *)
(* 					 	 	apply symmetry; assumption. *)
(* 					 	 	destruct s. rewrite <- p in r. *)
(* 					 	 	apply TotalOrder_Antisymmetric; assumption. *)
(* 					 	 	reflexivity. destruct s.  *)
(* 					 	 	assert ((py fst) = (pz snd)). apply TotalOrder_Antisymmetric. *)
(* 					 	 	apply (TotalOrder_Transitive (py fst) (px G5)); assumption. *)
(* 					 	 	assumption. rewrite X2. assert (px G5 = pz snd). *)
(* 					 	 	 apply TotalOrder_Antisymmetric. assumption. *)
(* 					 	 	 apply (TotalOrder_Transitive (pz snd) (py fst)); assumption. *)
(* 					 	 	 rewrite X3. *)
(* 					 	 	destruct ( TotalOrder_Total (pz snd) (pz snd)). *)
(* 					 	 	reflexivity. destruct s; reflexivity. *)
(* 					 	 	destruct (TotalOrder_Total (py fst) (pz snd)). *)
(* 					 	 		 apply TotalOrder_Antisymmetric.  assumption. rewrite p. *)
(* 					 	 	 apply (TotalOrder_Reflexive).  destruct s.  *)
(* 					 	 		 apply TotalOrder_Antisymmetric;  assumption. reflexivity. *)
(* - intros. rewrite transport_dom_eq_gen. *)
(*   apply path_forall. intro y0. cbn. *)
(*    destruct  *)
(*   		(union_non_empty' x y  *)
(*   		(transport (fun X : FSet A => X <> ∅) (comm x y)^ y0)) as  *)
(*   		[[Hx Hy] | [ [Ha Hb] | [Hc Hd]]]; *)
(*   	destruct (union_non_empty' y x y0) as  *)
(*   	   [[H'x H'y] | [ [H'a H'b] | [H'c H'd]]]; *)
(*   	   try (eq_neq_tac).  *)
(*      assert (Hx = H'b).  apply path_forall. intro. *)
(* 		 apply path_ishprop. rewrite X. reflexivity. *)
(* 		 assert (Hb = H'x).  apply path_forall. intro. *)
(* 		 apply path_ishprop. rewrite X. reflexivity. *)
(* 		  assert (Hd = H'c).  apply path_forall. intro. *)
(* 		 apply path_ishprop. rewrite X. *)
(* 		  assert (H'd = Hc).  apply path_forall. intro. *)
(* 		 apply path_ishprop. *)
(* 		 rewrite X0. rewrite <- X. *)
(* 	destruct  *)
(* 		(TotalOrder_Total (px Hc) (py Hd)) as [G1 | [G2 | G3]]; *)
(* 	destruct  *)
(* 	(TotalOrder_Total (py Hd) (px Hc)) as [T1 | [T2 | T3]]; *)
(* 	try (assumption); *)
(* 	try (reflexivity); *)
(* 	try (apply symmetry; assumption); *)
(* 	try (apply TotalOrder_Antisymmetric; assumption). *)
		 		  
(* - intros. rewrite transport_dom_eq_gen. *)
(*   apply path_forall. intro y. *)
(*   destruct (union_non_empty' ∅ x (transport (fun X : FSet A => X <> ∅) (nl x)^ y)). *)
(*   destruct p. eq_neq_tac.  *)
(*   destruct s.  *)
(*   destruct p. *)
(*   assert (y = snd). *)
(*     apply path_forall. intro. *)
(*     apply path_ishprop. rewrite X. reflexivity. *)
(*   destruct p. destruct fst. *)
(* - intros. rewrite transport_dom_eq_gen. *)
(*   apply path_forall. intro y. *)
(*   destruct (union_non_empty' x ∅ (transport (fun X : FSet A => X <> ∅) (nr x)^ y)). *)
(*   destruct p. assert (y = fst).  apply path_forall. intro. *)
(* apply path_ishprop. rewrite X. reflexivity. *)
(*   destruct s.  *)
(*   destruct p.  *)
(*   eq_neq_tac. *)
(*   destruct p. *)
(*   destruct snd. *)
(* - intros. rewrite transport_dom_eq_gen. *)
(* 	apply path_forall. intro y.  *)
(*   destruct ( union_non_empty' {|x|} {|x|} (transport (fun X : FSet A => X <> ∅) (idem x)^ y)). *)
(*   reflexivity. *)
(*   destruct s. *)
(*   reflexivity. *)
(*   destruct p. *)
(*   cbn. destruct  (TotalOrder_Total x x). reflexivity. *)
(*   destruct s; reflexivity. *)
(* Defined. *)
	

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
*)