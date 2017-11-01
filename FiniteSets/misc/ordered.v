(** If [A] has a total order, then we can pick the minimum of finite sets. *)
Require Import HoTT HitTactics.
Require Import HoTT.Classes.interfaces.orders.
Require Import kuratowski.kuratowski_sets kuratowski.operations kuratowski.properties.

Section minimum.
  Context {A : Type}.
  Context (Ale : Le A).
  Context `{@TotalOrder A Ale}.

  Class IsTop `{Top A} := is_top : forall (x : A), x ≤ ⊤.

  Definition min (x y : A) : A.
  Proof.
    destruct (total _ x y).
    - apply x.
    - apply y.
  Defined.

  Lemma min_spec1 x y : (min x y) ≤ x.
  Proof.
    unfold min.
    destruct (total _ x y) ; simpl.
    - reflexivity.
    - assumption.
  Defined.

  Lemma min_spec2 x y z : z ≤ x -> z ≤ y -> z ≤ (min x y).
  Proof.
    intros.
    unfold min.
    destruct (total _ x y); simpl; assumption.
  Defined.
  
  Lemma min_comm x y : min x y = min y x.
  Proof.
    unfold min.
    destruct (total _ x y) ; destruct (total _ y x) ; simpl; try reflexivity.
    + apply antisymmetry with (≤); [apply _|assumption..].
    + apply antisymmetry with (≤); [apply _|assumption..].
  Defined.

  Lemma min_idem x : min x x = x.
  Proof.
    unfold min.
    destruct (total _ x x) ; simpl; reflexivity.
  Defined.

  Lemma min_assoc x y z : min (min x y) z = min x (min y z).
  Proof.
    apply antisymmetry with (≤). apply _.
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
  
  Lemma min_nr `{IsTop} x : min x ⊤ = x.
  Proof.
    intros.
    unfold min.
    destruct (total _ x ⊤).
    - reflexivity.
    - apply antisymmetry with (≤). apply _.
      + assumption.
      + apply is_top.
  Defined.

  Lemma min_nl `{IsTop} x : min ⊤ x = x.
  Proof.
    rewrite min_comm.
    apply min_nr.
  Defined.

  Lemma min_top_l `{IsTop} x y : min x y = ⊤ -> x = ⊤.
  Proof.
    unfold min.
    destruct (total _ x y) as [?|s].
    - apply idmap.
    - intros X.
      rewrite X in s.
      apply antisymmetry with (≤). apply _.
      * apply is_top.
      * assumption.
  Defined.
  
  Lemma min_top_r `{IsTop} x y : min x y = ⊤ -> y = ⊤.
  Proof.
    rewrite min_comm.
    apply min_top_l.
  Defined.

End minimum.

Section add_top.
  Variable (A : Type).
  Context `{TotalOrder A}.

  Definition Topped := (A + Unit)%type.
  Global Instance top_topped : Top Topped := inr tt.

  Global Instance RTop : Le Topped.
  Proof.
    intros [a1 | ?] [a2 | ?].
    - apply (a1 ≤ a2).
    - apply Unit_hp.
    - apply False_hp.
    - apply Unit_hp.
  Defined.

  Instance rtop_hprop :
    is_mere_relation A R -> is_mere_relation Topped RTop.
  Proof.
    intros ? P a b.
    destruct a ; destruct b ; simpl; apply _.
  Defined.
  
  Global Instance RTopOrder : TotalOrder RTop.
  Proof.
    repeat split; try apply _.
    - intros [?|?] ; cbv.
      * reflexivity.
      * apply tt.
    - intros [a1 | []] [a2 | []] [a3 | []]; cbv
      ; try contradiction; try (by intros; apply tt).
      apply transitivity.
    - intros [a1 |[]] [a2 |[]]; cbv; try contradiction.
      + intros. f_ap. apply antisymmetry with Ale; [apply _|assumption..].
      + intros; reflexivity.
    - intros [a1|[]] [a2|[]]; cbv.
      * apply total. apply _.
      * apply (inl tt).
      * apply (inr tt).
      * apply (inr tt).
  Defined.

  Global Instance is_top_topped : IsTop RTop.
  Proof. intros [?|?]; cbv; apply tt. Defined.
End add_top.

(** If [A] has a total order, then a nonempty finite set has a minimum element. *)
Section min_set.
  Variable (A : Type).
  Context `{TotalOrder A}.
  Context `{Univalence} `{IsHSet A}.

  (* The reason why we put an additional element on top, is so that we can take the minimum of two results when considering union *)
  Definition min_set : FSet A -> Topped A.
  Proof.
    hrecursion.
    - apply ⊤.
    - apply inl.
    - apply min with (RTop A). apply _.
    - intros ; symmetry ; apply min_assoc.
    - apply min_comm.
    - apply min_nl. apply _.
    - apply min_nr. apply _.
    - intros ; apply min_idem.
  Defined.

  Definition empty_min : forall (X : FSet A), min_set X = ⊤ -> X = ∅.
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
    - intros x y ? ? ?.
      assert (min_set x = ⊤).
      { simple refine (min_top_l _ _ (min_set y) _) ; assumption. }
      rewrite (X X2).
      rewrite nl.
      assert (min_set y = ⊤).
      { simple refine (min_top_r _ (min_set x) _ _) ; assumption. }
      rewrite (X0 X3).
      reflexivity.
  Defined.
  
  Definition min_set_spec (a : A) : forall (X : FSet A),
      a ∈ X -> min_set X ≤ inl a.
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
        assert (RTop A (min _ (min_set x) (min_set y)) (min_set x)) as X1.
        { apply min_spec1. }
        etransitivity.
        { apply X1. }
        assumption.
      * specialize (X0 t).
        assert (RTop A (min _ (min_set x) (min_set y)) (min_set y)) as X1.
        { rewrite min_comm ; apply min_spec1. }
        etransitivity.
        { apply X1. }
        assumption.
  Defined.
End min_set.
