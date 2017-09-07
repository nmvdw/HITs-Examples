(** If [A] has a total order, then we can pick the minimum of finite sets. *)
Require Import HoTT HitTactics.
Require Import kuratowski.kuratowski_sets kuratowski.operations kuratowski.properties.

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

(** If [A] has a total order, then a nonempty finite set has a minimum element. *)
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