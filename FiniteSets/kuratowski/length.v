Require Import HoTT HitTactics prelude interfaces.lattice_interface interfaces.lattice_examples.
Require Import kuratowski.operations kuratowski.properties kuratowski.kuratowski_sets isomorphism.

Section length.
  Context {A : Type} `{MerelyDecidablePaths A} `{Univalence}.
  
  Definition length : FSet A -> nat.
    simple refine (FSet_cons_rec _ _ _ _ _ _).
    - apply 0%nat.
    - intros a X n.
      apply (if a ∈_d X then n else (S n)).
    - intros X a n.
      simpl.
      rewrite ?union_isIn_d, singleton_isIn_d_aa.
      reflexivity.
    - intros X a b n.
      simpl.
      rewrite ?union_isIn_d.
      destruct (m_dec_path a b) as [Hab | Hab].
      + strip_truncations.
        rewrite Hab.
        reflexivity.
      + rewrite ?singleton_isIn_d_false.
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
      apply (ap length (nl _)).
    - intros a X1 HX1 HX1Y.
      rewrite <- assoc, ?length_compute, ?union_isIn_d in *.
      pose (ap (fun Z => a ∈_d Z) HX1Y) as p.
      simpl in p.
      rewrite intersection_isIn_d, union_isIn_d, singleton_isIn_d_aa, empty_isIn_d in p.
      assert (orb (a ∈_d X1) (a ∈_d Y) = a ∈_d X1) as HaY.
      { destruct (a ∈_d X1), (a ∈_d Y) ; try reflexivity.
        contradiction true_ne_false.
      }
      rewrite ?HaY, HX1.
      destruct (a ∈_d X1) ; try reflexivity.
      apply (disjoint_sub a X1 Y HX1Y).
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
End length.

Section length_product.
  Context {A B : Type} `{MerelyDecidablePaths A} `{MerelyDecidablePaths B} `{Univalence}.
  
  Theorem length_singleproduct (a : A) (X : FSet B)
    : length (single_product a X) = length X.
  Proof.
    simple refine (FSet_cons_ind (fun Z => _) _ _ _ _ _ X)
    ; try (intros ; apply path_ishprop) ; simpl.
    - reflexivity.
    - intros b X1 HX1.
      rewrite ?length_compute, ?HX1.
      enough(b ∈_d X1 = (a, b) ∈_d (single_product a X1)) as HE.
      { rewrite HE ; reflexivity. }
      rewrite singleproduct_isIn_d_aa ; try reflexivity.
  Defined.  

  Open Scope nat.

  Lemma single_product_disjoint (a : A) (X1 : FSet A) (Y : FSet B)
        : sum (prod (a ∈_d X1 = true)
                        ((single_product a Y) ∪ (product X1 Y) = (product X1 Y)))
                  (prod (a ∈_d X1 = false)
                        (disjoint (single_product a Y) (product X1 Y))).
  Proof.
    pose (b := a ∈_d X1).
    assert (a ∈_d X1 = b) as HaX1.
    { reflexivity. }
    destruct b.
    * refine (inl(HaX1,_)).
      apply ext.
      intros [a1 b1].
      rewrite ?union_isIn_d.
      unfold member_dec, fset_member_bool in *.
      destruct (dec ((a1, b1) ∈ (single_product a Y))) as [t | t]
      ; destruct (dec ((a1, b1) ∈ (product X1 Y))) as [p | p]
      ; try reflexivity.
      rewrite singleproduct_isIn in t.
      destruct t as [t1 t2].
      rewrite product_isIn in p.
      strip_truncations.
      rewrite <- t1 in HaX1.
      destruct (dec (a1 ∈ X1)) ; try (contradiction false_ne_true).
      contradiction (p(t,t2)).
    * refine (inr(HaX1,_)).
      apply ext.
      intros [a1 b1].
      rewrite intersection_isIn_d, empty_isIn_d.
      unfold member_dec, fset_member_bool in *.
      destruct (dec ((a1, b1) ∈ (single_product a Y))) as [t | t]
      ; destruct (dec ((a1, b1) ∈ (product X1 Y))) as [p | p]
      ; try reflexivity.
      rewrite singleproduct_isIn in t ; destruct t as [t1 t2].
      rewrite product_isIn in p ; destruct p as [p1 p2].
      strip_truncations.
      rewrite t1 in p1.
      destruct (dec (a ∈ X1)).
      ** contradiction true_ne_false.
      ** contradiction (n p1).
  Defined.
    
  Theorem length_product (X : FSet A) (Y : FSet B)
    : length (product X Y) = length X * length Y.
  Proof.
    simple refine (FSet_cons_ind (fun Z => _) _ _ _ _ _ X)
    ; try (intros ; apply path_ishprop) ; simpl.
    - reflexivity.
    - intros a X1 HX1.
      rewrite length_compute.
      destruct (single_product_disjoint a X1 Y) as [[p1 p2] | [p1 p2]].
      * rewrite p2.
        destruct (a ∈_d X1).
        ** apply HX1.
        ** contradiction false_ne_true.
      * rewrite p1, length_disjoint, HX1 ; try assumption.
        rewrite length_singleproduct.
        reflexivity.
  Defined.
End length_product.

Section length_sum.
  Context `{Univalence}.
  Lemma length_fmap_inj
        {A B : Type} `{MerelyDecidablePaths A} `{MerelyDecidablePaths B}
        (X : FSet A) (f : A -> B) `{IsEmbedding f}
    : length (fset_fmap f X) = length X.
  Proof.
    simple refine (FSet_cons_ind (fun Z => _) _ _ _ _ _ X)
    ; try (intros ; apply path_ishprop) ; simpl.
    - reflexivity.
    - intros a Y HX.
      rewrite ?length_compute, HX, (fmap_isIn_d_inj _ f)
      ; auto.
  Defined.

  Context {A B : Type} `{MerelyDecidablePaths A} `{MerelyDecidablePaths B}.

  Lemma fmap_inl X a : (inl a) ∈_d (fset_fmap (@inr A B) X) = false.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - reflexivity.
    - intros b.
      rewrite singleton_isIn_d_false.
      * reflexivity.
      * apply inl_ne_inr.
    - intros X1 X2 HX1 HX2.
      rewrite union_isIn_d, HX1, HX2.
      reflexivity.
  Defined.
  
  Lemma fmap_inr X a : (inr a) ∈_d (fset_fmap (@inl A B) X) = false.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - reflexivity.
    - intros b.
      rewrite singleton_isIn_d_false.
      * reflexivity.
      * apply inr_ne_inl.
    - intros X1 X2 HX1 HX2.
      rewrite union_isIn_d, HX1, HX2.
      reflexivity.
  Defined.
  
  Lemma disjoint_summants X Y : disjoint (fset_fmap (@inl A B) X) (fset_fmap inr Y).
  Proof.
    apply ext.
    intros [x1 | x2] ; rewrite empty_isIn_d, intersection_isIn_d, ?fmap_inl, ?fmap_inr
    ; simpl ; try reflexivity.
    destruct ((inl x1) ∈_d (fset_fmap inl X)) ; reflexivity.
  Defined.

  Open Scope nat.
  
  Theorem length_disjoint_sum (X : FSet A) (Y : FSet B)
    : length (disjoint_sum X Y) = length X + length Y.
  Proof.
    rewrite (length_disjoint _ _ (disjoint_summants _ _)).
    rewrite ?(length_fmap_inj _ _).
    reflexivity.
  Defined.
End length_sum.

Section length_zero_one.
  Context {A : Type} `{Univalence} `{MerelyDecidablePaths A}.

  Lemma Z_not_S n : S n = 0%nat -> Empty.
  Proof.
    refine (@equiv_path_nat (n.+1) 0)^-1.
  Defined.

  Lemma remove_S n m : S n = S m -> n = m.
  Proof.
    intros X.
    enough (n.+1 =n m.+1) as X0.
    {
      simpl in X0.
      apply (equiv_path_nat X0).
    }
    apply ((equiv_path_nat)^-1 X).
  Defined.
  
  Theorem length_zero : forall (X : FSet A) (HX : length X = 0%nat), X = ∅.
  Proof.
    simple refine (FSet_cons_ind (fun Z => _) _ _ _ _ _)
    ; try (intros ; apply path_ishprop) ; simpl.
    - reflexivity.
    - intros a X HX HaX.
      rewrite length_compute in HaX.
      unfold member_dec, fset_member_bool in HaX.
      destruct (dec (a ∈ X)).
      * pose (HX HaX) as XE.
        pose (transport (fun Z => a ∈ Z) XE t) as Nonsense.
        contradiction Nonsense.        
      * contradiction (Z_not_S _ HaX).
  Defined.  

  Theorem length_one : forall (X : FSet A) (HX : length X = 1%nat), hexists (fun a => X = {|a|}).
  Proof.
    simple refine (FSet_cons_ind (fun Z => _) _ _ _ _ _)
    ; try (intros ; apply path_ishprop) ; simpl.
    - intros.
      contradiction (Z_not_S _ (HX^)).
    - intros a X HX HaX.
      refine (tr(a;_)).
      rewrite length_compute in HaX.
      unfold member_dec, fset_member_bool in HaX.
      destruct (dec (a ∈ X)).
      * specialize (HX HaX).
        strip_truncations.
        destruct HX as [b HX].
        assert (({|a|} : FSet A) = {|b|}) as p.
        {
          rewrite HX in t.
          strip_truncations.
          f_ap.
        }
        rewrite HX, p.
        apply union_idem.
      * rewrite (length_zero _ (remove_S _ _ HaX)).
        apply nr.
  Defined.
End length_zero_one.
