Require Import HoTT HitTactics prelude interfaces.lattice_interface interfaces.lattice_examples.
Require Import kuratowski.operations kuratowski.properties kuratowski.kuratowski_sets isomorphism.

Section Length.
  Context {A : Type} `{MerelyDecidablePaths A} `{Univalence}.
  
  Definition length : FSet A -> nat.
    simple refine (FSet_cons_rec _ _ _ _ _ _).
    - apply 0.
    - intros a X n.
      apply (if a ∈_d X then n else (S n)).
    - intros X a n.
      simpl.
      simplify_isIn_d.
      destruct (dec (a ∈ X)) ; reflexivity.
    - intros X a b n.
      simpl.
      simplify_isIn_d.
      destruct (m_dec_path a b) as [Hab | Hab].
      + strip_truncations.
        rewrite Hab. simplify_isIn_d. reflexivity.
      + rewrite ?singleton_isIn_d_false; auto.
        ++ simpl. 
           destruct (a ∈_d X), (b ∈_d X) ; reflexivity.
        ++ intro p. contradiction (Hab (tr p^)).
        ++ intros p.
           apply (Hab (tr p)).          
  Defined.

  Open Scope nat.
  (** Specification for length. *)
  Definition length_empty : length ∅ = 0 := idpath.
  
  Definition length_singleton a : length {|a|} = 1 := idpath.

  Lemma length_compute (a : A) (X : FSet A) :
    length ({|a|} ∪ X) = if (a ∈_d X) then length X else S(length X).
  Proof.
    unfold length.
    rewrite FSet_cons_beta_cons.
    reflexivity.
  Defined.
  
  Definition length_add (a : A) (X : FSet A) (p : a ∈_d X = false)
             : length ({|a|} ∪ X) = 1 + (length X).
  Proof.
    rewrite length_compute.
    destruct (a ∈_d X).
    - contradiction (true_ne_false).
    - reflexivity.
  Defined.

  Definition disjoint X Y := X ∩ Y = ∅.

  Lemma disjoint_difference X Y : disjoint X (difference Y X).
  Proof.
    apply ext.
    intros a.
    rewrite intersection_isIn_d, empty_isIn_d, difference_isIn_d.
    destruct (a ∈_d X), (a ∈_d Y) ; try reflexivity.
  Defined.

  Lemma disjoint_sub a X Y (H1 : disjoint ({|a|} ∪ X) Y) : disjoint X Y.
  Proof.
    unfold disjoint in *.
    apply ext.
    intros b.
    simplify_isIn_d.
    rewrite empty_isIn_d.
    pose (ap (fun Z => b ∈_d Z) H1) as p.
    simpl in p.
    rewrite intersection_isIn_d, empty_isIn_d, union_isIn_d in p.
    destruct (b ∈_d X), (b ∈_d Y) ; try reflexivity.
    - destruct (b ∈_d {|a|}) ; simpl in * ; try (contradiction true_ne_false).
  Defined.  

  Definition length_disjoint (X Y : FSet A) :
    forall (HXY : disjoint X Y),
      length (X ∪ Y) = (length X) + (length Y).
  Proof.
    simple refine (FSet_cons_ind (fun Z => _) _ _ _ _ _ X)
    ; try (intros ; apply path_ishprop) ; simpl.
    - intros.
      rewrite nl.
      reflexivity.
    - intros a X1 HX1 HX1Y.
      rewrite <- assoc.
      rewrite ?length_compute.
      rewrite ?union_isIn_d in *.
      unfold disjoint in HX1Y.
      pose (ap (fun Z => a ∈_d Z) HX1Y) as p.
      simpl in p.
      rewrite intersection_isIn_d, union_isIn_d, singleton_isIn_d_aa, empty_isIn_d in p.
      assert (orb (a ∈_d X1) (a ∈_d Y) = a ∈_d X1) as HaY.
      { destruct (a ∈_d X1), (a ∈_d Y) ; try reflexivity.
        contradiction true_ne_false.
      }
      rewrite ?HaY, HX1.
      destruct (a ∈_d X1).
      * reflexivity.
      * reflexivity.
      * apply (disjoint_sub a X1 Y HX1Y).
  Defined.

  Lemma set_as_difference X Y : X = (difference X Y) ∪ (X ∩ Y).
  Proof.
    toBool.
    generalize (a ∈_d X), (a ∈_d Y).
    intros b c ; destruct b, c ; reflexivity.
  Defined.
  
  Lemma length_single_disjoint (X Y : FSet A) :
    length X = length (difference X Y) + length (X ∩ Y).
  Proof.
    refine (ap length (set_as_difference X Y) @ _).
    apply length_disjoint.
    apply ext.
    intros a.
    rewrite ?intersection_isIn_d, empty_isIn_d, difference_isIn_d.
    destruct (a ∈_d X), (a ∈_d Y) ; try reflexivity.
  Defined.

  Lemma union_to_disjoint X Y : X ∪ Y = X ∪ (difference Y X).
  Proof.
    toBool.
    generalize (a ∈_d X), (a ∈_d Y).
    intros b c ; destruct b, c ; reflexivity.
  Defined.
  
  Lemma length_union_1 (X Y : FSet A) :
    length (X ∪ Y) = length X + length (difference Y X).
  Proof.
    refine (ap length (union_to_disjoint X Y) @ _).
    apply length_disjoint.
    apply ext.
    intros a.
    rewrite ?intersection_isIn_d, empty_isIn_d, difference_isIn_d.
    destruct (a ∈_d X), (a ∈_d Y) ; try reflexivity.
  Defined.

  Lemma plus_assoc n m k : n + (m + k) = (n + m) + k.
  Proof.
    induction n ; simpl.
    - reflexivity.
    - rewrite IHn.
      reflexivity.
  Defined.
  
  Lemma inclusion_exclusion (X Y : FSet A) :
    length (X ∪ Y) + length (Y ∩ X) = length X + length Y.
  Proof.
    rewrite length_union_1.
    rewrite (length_single_disjoint Y X).
    rewrite plus_assoc.
    reflexivity.
  Defined.
  
End Length.