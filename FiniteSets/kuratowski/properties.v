Require Import HoTT HitTactics prelude.
Require Import kuratowski.extensionality kuratowski.operations kuratowski_sets.
Require Import lattice_interface lattice_examples monad_interface.

(** [FSet] is a (strong and stable) finite powerset monad *)
Section monad_fset.
  Context `{Funext}.

  Global Instance functorish_fset : Functorish FSet.
  Proof.
    simple refine (Build_Functorish _ _ _).
    - intros ? ? f.
      apply (fset_fmap f).
    - intros A.
      apply path_forall.
      intro x.
      hinduction x
      ; try (intros ; f_ap)
      ; try (intros ; apply path_ishprop).
  Defined.

  Global Instance functor_fset : Functor FSet.
  Proof.
    split.
    intros.
    apply path_forall.
    intro x.
    hrecursion x
    ; try (intros ; f_ap)
    ; try (intros ; apply path_ishprop).
  Defined.

  Global Instance monad_fset : Monad FSet.
  Proof.
    split.
    - intros. reflexivity.
    - intros A X.
      hrecursion X;
        try (intros; compute[bind ret bind_fset return_fset]; simpl; f_ap);
        try (intros; apply path_ishprop); try reflexivity.
    - intros A B C X f g.
      hrecursion X;
        try (intros; compute[bind ret bind_fset return_fset]; simpl; f_ap);
        try (intros; apply path_ishprop); try reflexivity.
  Defined.

  Lemma fmap_isIn `{Univalence} {A B : Type} (f : A -> B) (a : A) (X : FSet A) :
    a ∈ X -> (f a) ∈ (fmap FSet f X).
  Proof.
    hinduction X; try (intros; apply path_ishprop).
    - apply idmap.
    - intros b Hab; strip_truncations.
      apply (tr (ap f Hab)).
    - intros X0 X1 HX0 HX1 Ha.
      strip_truncations. apply tr.
      destruct Ha as [Ha | Ha].
      + left. by apply HX0.
      + right. by apply HX1.
  Defined.

  Instance surjection_fmap `{Univalence} {A B : Type} (f : A -> B)
    {Hsurj : IsSurjection f} : IsSurjection (fmap FSet f).
  Proof.
    apply BuildIsSurjection.
    hinduction; try (intros; apply path_ishprop).
    - apply tr. exists ∅. reflexivity.
    - intro b.
      specialize (Hsurj b).
      cbv in Hsurj.
      destruct Hsurj as [Hsurj _].
      strip_truncations.
      destruct Hsurj as [a Ha].
      apply tr.
      exists {|a|}. simpl. f_ap.
    - intros X Y HX HY.
      strip_truncations.
      apply tr.
      destruct HY as [Y' HY].
      destruct HX as [X' HX].
      exists (X' ∪ Y'). simpl.
      f_ap.
  Defined.

  Lemma mjoin_isIn `{Univalence} {A : Type} (X : FSet (FSet A)) (a : A) :
    (exists x, prod (x ∈ X) (a ∈ x)) -> a ∈ (mjoin X).
  Proof.
    hinduction X;
      try (intros; apply path_forall; intro; apply path_ishprop).
    - simpl. intros [x [[] ?]].
    - intros x [y [Hx Hy]].
      strip_truncations.
      rewrite <- Hx.
      apply Hy.
    - intros x x' IHx IHx'.
      intros [z [Hz Ha]].
      strip_truncations.
      apply tr.
      destruct Hz as [Hz | Hz]; [ left | right ].
      + apply IHx.
        exists z. split; assumption.
      + apply IHx'.
        exists z. split; assumption.
  Defined.

  (* So other properties of FSet(-) as acting on objects *)
  (* Elephant D Cor 5.4.5 *)
  Definition FSet_Unit_2 : FSet Unit -> Unit + Unit.
  Proof.
    hinduction.
    - left. apply tt.
    - intros []. right. apply tt.
    - intros A B.
      destruct A.
      + destruct B.
        * left. apply tt.
        * right. apply tt.
      + right. apply tt.
    - intros [[] | []] [[] | []] [[] | []]; reflexivity.
    - intros [[] | []] [[] | []]; reflexivity.
    - intros [[] | []]; reflexivity.
    - intros [[] | []]; reflexivity.
    - intros []; reflexivity.
  Defined.

  Definition Two_FSet_Unit : Unit + Unit -> FSet Unit.
  Proof.
    intros [[] | []].
    - exact ∅.
    - exact {|tt|}.
  Defined.

  Lemma FSet_Unit : FSet Unit <~> Unit + Unit.
  Proof.
    apply BuildEquiv with FSet_Unit_2.
    apply equiv_biinv_isequiv.
    split; exists Two_FSet_Unit.
    - intro x. hrecursion x.
      + reflexivity.
      + intros []. reflexivity.
      + intros X Y HX HY.
        destruct (FSet_Unit_2 X) as [[] | []], (FSet_Unit_2 Y) as [[] | []];
          rewrite <- HX; rewrite <- HY; simpl.
        * apply (union_idem _)^.
        * apply (nl _)^.
        * apply (nr _)^.
        * apply (union_idem _)^.
      + intros. apply path_ishprop.
      + intros. apply path_ishprop.
      + intros. apply path_ishprop.
      + intros. apply path_ishprop.
      + intros. apply path_ishprop.
    - intros [[] | []]; simpl; reflexivity.
  Defined.
  
  Definition fsum1 {A B : Type} : FSet (A + B) -> FSet A * FSet B.
  Proof.
    hrecursion.
    - exact (∅, ∅).
    - intros [a | b].
      + exact ({|a|}, ∅).
      + exact (∅, {|b|}).
    - intros [X Y] [X' Y'].
      exact (X ∪ X', Y ∪ Y').
    - intros [X X'] [Y Y'] [Z Z'].
      rewrite !assoc.
      reflexivity.
    - intros [X X'] [Y Y'].
      rewrite (comm Y X).
      rewrite (comm Y' X').
      reflexivity.
    - intros [X X'].
      rewrite !nl.
      reflexivity.
    - intros [X X'].
      rewrite !nr.
      reflexivity.
    - intros [a | b]; simpl; rewrite !union_idem; reflexivity.
  Defined.
  
  Definition fsum2 {A B : Type} : FSet A * FSet B -> FSet (A + B).
  Proof.
    intros [X Y].
    exact ((fset_fmap inl X) ∪ (fset_fmap inr Y)).
  Defined.
  
  Lemma fsum1_inl {A B : Type} (X : FSet A) :
    fsum1 (fset_fmap inl X) = (X, ∅ : FSet B).
  Proof.
    hinduction X; try reflexivity; try (intros; apply path_ishprop).
    intros X Y HX HY.
    rewrite HX, HY. simpl.
    rewrite nl.
    reflexivity.
  Defined.
  
  Lemma fsum1_inr {A B : Type} (Y : FSet B) :
    fsum1 (fset_fmap inr Y) = (∅ : FSet A, Y).
  Proof.
    hinduction Y; try reflexivity; try (intros; apply path_ishprop).
    intros X Y HX HY.
    rewrite HX, HY. simpl.
    rewrite nl.
    reflexivity.
  Defined.
  
  Lemma FSet_sum {A B : Type}: FSet (A + B) <~> FSet A * FSet B.
  Proof.
    apply BuildEquiv with fsum1.
    apply equiv_biinv_isequiv.
    split; exists fsum2.
    - intros X. hrecursion X; unfold fsum2; simpl.
      + apply nl.
      + intros [a | b]; simpl; [apply nr | apply nl].
      + intros X Y HX HY.
        destruct (fsum1 X) as [X1 X2].
        destruct (fsum1 Y) as [Y1 Y2].
        rewrite (comm _ (fset_fmap inr Y2)).
        rewrite <-assoc.
        rewrite (assoc (fset_fmap inl Y1)).
        rewrite HY.
        rewrite (comm Y).
        rewrite assoc.
        rewrite HX.
        reflexivity.
      + intros. apply path_ishprop.
      + intros. apply path_ishprop.
      + intros. apply path_ishprop.
      + intros. apply path_ishprop.
      + intros. apply path_ishprop.
    - intros [X Y]. simpl.
      rewrite !fsum1_inl, !fsum1_inr.
      simpl.
      rewrite nl, nr.
      reflexivity.
  Defined.
End monad_fset.

(** Lemmas relating operations to the membership predicate *)
Section properties_membership.
  Context {A : Type} `{Univalence}.

  Definition empty_isIn (a: A) : a ∈ ∅ -> Empty := idmap.

  Definition singleton_isIn (a b: A) : a ∈ {|b|} -> Trunc (-1) (a = b) := idmap.

  Definition union_isIn (X Y : FSet A) (a : A)
    : a ∈ X ∪ Y = a ∈ X ∨ a ∈ Y := idpath.

  Lemma comprehension_union (ϕ : A -> Bool) : forall X Y : FSet A,
      {| (X ∪ Y) | ϕ|} = {|X | ϕ|} ∪ {|Y | ϕ|}.
  Proof.
    reflexivity.
  Defined.

  Lemma comprehension_isIn (ϕ : A -> Bool) (a : A) : forall X : FSet A,
      a ∈ {|X | ϕ|} = if ϕ a then a ∈ X else False_hp.
  Proof.
    hinduction ; try (intros ; apply set_path2).
    - destruct (ϕ a) ; reflexivity.
    - intros b.
      assert (forall c d, ϕ a = c -> ϕ b = d ->
                          a ∈ (if ϕ b then {|b|} else ∅)
                          =
                          (if ϕ a then BuildhProp (Trunc (-1) (a = b)) else False_hp)) as X.
      {
        intros c d Hc Hd.
        destruct c ; destruct d ; rewrite Hc, Hd ; try reflexivity
        ; apply path_iff_hprop ; try contradiction ; intros ; strip_truncations
        ; apply (false_ne_true).
        * apply (Hd^ @ ap ϕ X^ @ Hc).
        * apply (Hc^ @ ap ϕ X @ Hd).
      }
      apply (X (ϕ a) (ϕ b) idpath idpath).
    - intros X Y H1 H2.
      rewrite comprehension_union.
      rewrite union_isIn.
      rewrite H1, H2.
      destruct (ϕ a).
      * reflexivity.
      * apply path_iff_hprop.
        ** intros Z ; strip_truncations.
           destruct Z ; assumption.
        ** intros ; apply tr ; right ; assumption.
  Defined.

  Context {B : Type}.

  Lemma singleproduct_isIn (a : A) (b : B) (c : A) : forall (Y : FSet B),
      (a, b) ∈ (single_product c Y) = land (BuildhProp (Trunc (-1) (a = c))) (b ∈ Y).
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - apply path_hprop ; symmetry ; apply prod_empty_r.
    - intros d.
      apply path_iff_hprop.
      * intros.
        strip_truncations.
        split ; apply tr ; try (apply (ap fst X)) ; try (apply (ap snd X)).
      * intros [Z1 Z2].
        strip_truncations.
        rewrite Z1, Z2.
        apply (tr idpath).
    - intros X1 X2 HX1 HX2.
      apply path_iff_hprop ; rewrite ?union_isIn.
      * intros X.
        cbn in *.
        strip_truncations.
        destruct X as [H1 | H1] ; rewrite ?HX1, ?HX2 in H1
        ; destruct H1 as [H1 H2].
        ** split.
           *** apply H1.
           *** apply (tr(inl H2)).
        ** split.
           *** apply H1.
           *** apply (tr(inr H2)).
      * intros [H1 H2].
        cbn in *.
        strip_truncations.
        apply tr.
        rewrite HX1, HX2.
        destruct H2 as [Hb1 | Hb2].
        ** left.
           split ; try (apply (tr H1)) ; try (apply Hb1).
        ** right.
           split ; try (apply (tr H1)) ; try (apply Hb2).
  Defined.

  Definition product_isIn (a : A) (b : B) (X : FSet A) (Y : FSet B) :
    (a,b) ∈ (product X Y) = land (a ∈ X) (b ∈ Y).
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - apply path_hprop ; symmetry ; apply prod_empty_l.
    - intros.
      apply singleproduct_isIn.
    - intros X1 X2 HX1 HX2.
      cbn.
      rewrite HX1, HX2.
      apply path_iff_hprop ; rewrite ?union_isIn.
      * intros X.
        strip_truncations.
        destruct X as [[H3 H4] | [H3 H4]] ; split ; try (apply H4).
        ** apply (tr(inl H3)).
        ** apply (tr(inr H3)).
      * intros [H1 H2].
        strip_truncations.
        destruct H1 as [H1 | H1] ; apply tr.
        ** left ; split ; assumption.
        ** right ; split ; assumption.
  Defined.
  
  Lemma separation_isIn : forall (X : FSet A) (f : {a | a ∈ X} -> B) (b : B),
      b ∈ (separation A B X f) = hexists (fun a : A => hexists (fun (p : a ∈ X) => f (a;p) = b)).
  Proof.
    hinduction ; try (intros ; apply path_forall ; intro ; apply path_ishprop).
    - intros ; simpl.
      apply path_iff_hprop ; try contradiction.
      intros X.
      strip_truncations.
      destruct X as [a X].
      strip_truncations.
      destruct X as [p X].
      assumption.
    - intros.
      apply path_iff_hprop ; simpl.
      * intros ; strip_truncations.
        apply tr.
        exists a.
        apply tr.
        exists (tr idpath).
        apply X^.
      * intros X ; strip_truncations.
        destruct X as [a0 X].
        strip_truncations.
        destruct X as [X q].
        simple refine (Trunc_ind _ _ X).
        intros p.
        apply tr.
        rewrite <- q.
        f_ap.
        simple refine (path_sigma _ _ _ _ _).
        ** apply p.
        ** apply path_ishprop.
    - intros X1 X2 HX1 HX2 f b.
      pose (fX1 := fun Z : {a : A | a ∈ X1} => f (pr1 Z;tr (inl (pr2 Z)))).
      pose (fX2 := fun Z : {a : A | a ∈ X2} => f (pr1 Z;tr (inr (pr2 Z)))).
      specialize (HX1 fX1 b).
      specialize (HX2 fX2 b).
      apply path_iff_hprop.
      * intros X.
        cbn in *.
        strip_truncations.
        destruct X as [X | X].
        ** rewrite HX1 in X.
           strip_truncations.
           destruct X as [a Ha].
           apply tr.
           exists a.
           strip_truncations.
           destruct Ha as [p pa].
           apply tr.
           exists (tr(inl p)).
           rewrite <- pa.
           reflexivity.
        ** rewrite HX2 in X.
           strip_truncations.
           destruct X as [a Ha].
           apply tr.
           exists a.
           strip_truncations.
           destruct Ha as [p pa].
           apply tr.
           exists (tr(inr p)).
           rewrite <- pa.
           reflexivity.
      * intros.
        strip_truncations.
        destruct X as [a X].
        strip_truncations.
        destruct X as [Ha p].
        cbn.
        simple refine (Trunc_ind _ _ Ha) ; intros [Ha1 | Ha2].
        ** refine (tr(inl _)).
           rewrite HX1.
           apply tr.
           exists a.
           apply tr.
           exists Ha1.
           rewrite <- p.
           unfold fX1.
           repeat f_ap.
           apply path_ishprop.
        ** refine (tr(inr _)).
           rewrite HX2.
           apply tr.
           exists a.
           apply tr.
           exists Ha2.
           rewrite <- p.
           unfold fX2.
           repeat f_ap.
           apply path_ishprop.
  Defined.

  Lemma fmap_isIn_inj (f : A -> B) (a : A) (X : FSet A) {f_inj : IsEmbedding f} :
    a ∈ X = (f a) ∈ (fmap FSet f X).
  Proof.
    hinduction X; try (intros; apply path_ishprop).
    - reflexivity.
    - intros b.
      apply path_iff_hprop.
      * intros Ha.
        strip_truncations.
        apply (tr (ap f Ha)).
      * intros Hfa.
        strip_truncations.
        apply tr.
        unfold IsEmbedding, hfiber in *.
        specialize (f_inj (f a)).
        pose ((a;idpath (f a)) : {x : A | f x = f a}) as p1.
        pose ((b;Hfa^) : {x : A | f x = f a}) as p2.
        assert (p1 = p2) as Hp1p2.
        { apply f_inj. }
        apply (ap (fun x => x.1) Hp1p2).
    - intros X0 X1 HX0 HX1.
      rewrite ?union_isIn, HX0, HX1.
      reflexivity.
  Defined.
End properties_membership.

Ltac simplify_isIn :=
  repeat (rewrite union_isIn
          || rewrite comprehension_isIn).

Ltac toHProp :=
  repeat intro;
  apply fset_ext ; intros ;
  simplify_isIn ; eauto with lattice_hints typeclass_instances.

(** [FSet A] is a join semilattice. *)
Section fset_join_semilattice.
  Context {A : Type}.

  Global Instance bottom_fset : Bottom (FSet A) := ∅.

  Global Instance join_fset : Join (FSet A) := fun x y => x ∪ y.

  Global Instance boundedjoinsemilattice_fset : BoundedJoinSemiLattice (FSet A).
  Proof.
    repeat split; try apply _; cbv.
    - apply assoc.
    - apply nl.
    - apply nr.
    - apply comm.
    - apply union_idem.
  Defined.  
End fset_join_semilattice.

(* Lemmas relating operations to the membership predicate *)
Section properties_membership_decidable.
  Context {A : Type} `{MerelyDecidablePaths A} `{Univalence}.

  Lemma ext : forall (S T : FSet A), (forall a, a ∈_d S = a ∈_d T) -> S = T.
  Proof.
    intros X Y H2.
    apply fset_ext.
    intro a.
    specialize (H2 a).
    unfold member_dec, fset_member_bool, dec in H2.
    destruct (isIn_decidable a X) ; destruct (isIn_decidable a Y).
    - apply path_iff_hprop ; intro ; assumption.
    - contradiction (true_ne_false).
    - contradiction (true_ne_false) ; apply H2^.
    - apply path_iff_hprop ; intro ; contradiction.
  Defined.

  Definition empty_isIn_d (a : A) : a ∈_d ∅ = false := idpath.

  Lemma singleton_isIn_d_true (a b : A) (p : a = b) :
    a ∈_d {|b|} = true.
  Proof.
    unfold member_dec, fset_member_bool, dec.
    destruct (isIn_decidable a {|b|}) as [n | n] .
    - reflexivity.
    - simpl in n.
      contradiction (n (tr p)).
  Defined.

  Lemma singleton_isIn_d_aa (a : A) :
    a ∈_d {|a|} = true.
  Proof.
    apply singleton_isIn_d_true ; reflexivity.
  Defined.

  Lemma singleton_isIn_d_false (a b : A) (p : a <> b) :
    a ∈_d {|b|} = false.
  Proof.
    unfold member_dec, fset_member_bool, dec in *.
    destruct (isIn_decidable a {|b|}).
    - simpl in t.
      strip_truncations.
      contradiction.
    - reflexivity.
  Defined.

  Lemma union_isIn_d (X Y : FSet A) (a : A) :
    a ∈_d (X ∪ Y) = orb (a ∈_d X) (a ∈_d Y).
  Proof.
    unfold member_dec, fset_member_bool, dec.
    simpl.
    destruct (isIn_decidable a X) ; destruct (isIn_decidable a Y) ; reflexivity.
  Defined.

  Lemma comprehension_isIn_d (Y : FSet A) (ϕ : A -> Bool) (a : A) :
    a ∈_d {|Y | ϕ|} = andb (a ∈_d Y) (ϕ a).
  Proof.
    unfold member_dec, fset_member_bool, dec ; simpl.
    destruct (isIn_decidable a {|Y | ϕ|}) as [t | t]
    ; destruct (isIn_decidable a Y) as [n | n] ; rewrite comprehension_isIn in t
    ; destruct (ϕ a) ; try reflexivity ; try contradiction
    ; try (contradiction (n t)) ; contradiction (t n).
  Defined.

  Lemma intersection_isIn_d (X Y: FSet A) (a : A) :
    a ∈_d (X ∩ Y) = andb (a ∈_d X) (a ∈_d Y).
  Proof.
    apply comprehension_isIn_d.
  Defined.

  Lemma intersection_isIn (X Y: FSet A) (a : A) :
    a ∈ (X ∩ Y) = BuildhProp ((a ∈ X) * (a ∈ Y)).
  Proof.
    unfold intersection, fset_intersection.
    rewrite comprehension_isIn.
    unfold member_dec, fset_member_bool.
    destruct (dec (a ∈ Y)) as [? | n].
    - apply path_iff_hprop ; intros X0
      ; try split ; try (destruct X0) ; try assumption.
    - apply path_iff_hprop ; try contradiction.
      intros [? p].
      apply (n p).
  Defined.

  Lemma difference_isIn_d (X Y: FSet A) (a : A) :
    a ∈_d (difference X Y) = andb (a ∈_d X) (negb (a ∈_d Y)).
  Proof.
    apply comprehension_isIn_d.
  Defined.  

  Context (B : Type) `{MerelyDecidablePaths A} `{MerelyDecidablePaths B}.

  Lemma fmap_isIn_d_inj (f : A -> B) (a : A) (X : FSet A) {f_inj : IsEmbedding f} :
    a ∈_d X = (f a) ∈_d (fmap FSet f X).
  Proof.
    unfold member_dec, fset_member_bool, dec.
    destruct (isIn_decidable a X) as [t | t], (isIn_decidable (f a) (fmap FSet f X)) as [n | n]
    ; try reflexivity.
    - rewrite <- fmap_isIn_inj in n ; try (apply _).
      contradiction (n t).
    - rewrite <- fmap_isIn_inj in n ; try (apply _).
      contradiction (t n).
  Defined.
  
  Lemma singleton_isIn_d `{IsHSet A} (a b : A) :
    a ∈ {|b|} -> a = b.
  Proof.
    intros.
    strip_truncations.
    assumption.
  Defined.
End properties_membership_decidable.

Section product_membership.
  Context {A B : Type} `{MerelyDecidablePaths A} `{MerelyDecidablePaths B} `{Univalence}.
  
  Lemma singleproduct_isIn_d_aa (a : A) (b : B) (c : A) (p : c = a) (Y : FSet B) :
      (a, b) ∈_d (single_product c Y) = b ∈_d Y.
  Proof.
    unfold member_dec, fset_member_bool, dec ; simpl.
    destruct (isIn_decidable (a, b) (single_product c Y)) as [t | t]
    ; destruct (isIn_decidable b Y) as [n | n]
    ; try reflexivity.
    * rewrite singleproduct_isIn in t.
      destruct t as [t1 t2].
      contradiction (n t2).
    * rewrite singleproduct_isIn in t.
      contradiction (t (tr(p^),n)).
  Defined.

  Lemma singleproduct_isIn_d_false (a : A) (b : B) (c : A) (p : c = a -> Empty) (Y : FSet B) :
    (a, b) ∈_d (single_product c Y) = false.
  Proof.
    unfold member_dec, fset_member_bool, dec ; simpl.
    destruct (isIn_decidable (a, b) (single_product c Y)) as [t | t]
    ; destruct (isIn_decidable b Y) as [n | n]
    ; try reflexivity.
    * rewrite singleproduct_isIn in t.
      destruct t as [t1 t2].
      strip_truncations.
      contradiction (p t1^).
    * rewrite singleproduct_isIn in t.
      contradiction (n (snd t)).
  Defined.

  Lemma product_isIn_d (a : A) (b : B) (X : FSet A) (Y : FSet B) :
    (a, b) ∈_d (product X Y) = andb (a ∈_d X) (b ∈_d Y).
  Proof.
    unfold member_dec, fset_member_bool, dec ; simpl.
    destruct (isIn_decidable (a, b) (product X Y)) as [t | t]
    ; destruct (isIn_decidable a X) as [n1 | n1]
    ; destruct (isIn_decidable b Y) as [n2 | n2]
    ; try reflexivity
    ; rewrite ?product_isIn in t
    ; try (destruct t as [t1 t2]
           ; contradiction (n1 t1) || contradiction (n2 t2)).
    contradiction (t (n1, n2)).
  Defined.
End product_membership.  
  
(* Some suporting tactics *)
Ltac simplify_isIn_d :=
  repeat (rewrite union_isIn_d
        || rewrite singleton_isIn_d_aa
        || rewrite intersection_isIn_d
        || rewrite comprehension_isIn_d).

Ltac toBool :=
  repeat intro;
  apply ext ; intros ;
  simplify_isIn_d ; eauto with bool_lattice_hints typeclass_instances.

(** If `A` has decidable equality, then `FSet A` is a lattice *) 
Section set_lattice.
  Context {A : Type}.
  Context `{MerelyDecidablePaths A}.
  Context `{Univalence}.

  Global Instance meet_fset : Meet (FSet A) := intersection.

  Global Instance lattice_fset : Lattice (FSet A).
  Proof.
    repeat split; try apply _;
      compute[sg_op meet_is_sg_op meet_fset];
      toBool.
    apply associativity.
  Defined.
End set_lattice.

(** If `A` has decidable equality, then so has `FSet A`. *)
Section dec_eq.
  Context {A : Type} `{DecidablePaths A} `{Univalence}.

  Global Instance dec_eq_fset : DecidablePaths (FSet A).
  Proof.
    intros X Y.
    apply (decidable_equiv' ((Y ⊆ X) * (X ⊆ Y)) (eq_subset X Y)^-1).
    apply decidable_prod.
  Defined.
End dec_eq.

(** comprehension properties *)
Section comprehension_properties.
  Context {A : Type} `{Univalence}.

  Lemma comprehension_false : forall (X : FSet A), {|X | fun _ => false|} = ∅.
  Proof.
    toHProp.
  Defined.

  Lemma comprehension_subset : forall ϕ (X : FSet A),
      {|X | ϕ|} ∪ X = X.
  Proof.
    toHProp.
    destruct (ϕ a) ; eauto with lattice_hints typeclass_instances.
    - apply binary_idempotent.
    - apply left_identity.
  Defined.

  Lemma comprehension_or : forall ϕ ψ (X : FSet A),
      {|X | (fun a => orb (ϕ a) (ψ a))|}
      = {|X | ϕ|} ∪ {|X | ψ|}.
  Proof.
    toHProp.
    symmetry ; destruct (ϕ a) ; destruct (ψ a)
    (* ; eauto with lattice_hints typeclass_instances; *)
    ; simpl; (apply binary_idempotent || apply left_identity || apply right_identity).
  Defined.

  Lemma comprehension_all : forall (X : FSet A),
      {|X | fun _ => true|} = X.
  Proof.
    toHProp.
  Defined.
End comprehension_properties.

(** For [FSet A] we have mere choice. *)
Section mere_choice.
  Context {A : Type} `{Univalence}.

  Local Ltac solve_mc :=
    repeat (let x := fresh in intro x ; try(destruct x))
    ; simpl
    ; rewrite transport_sum
    ; try (f_ap ; apply path_ishprop)
    ; try (f_ap ; apply set_path2).

  Lemma merely_choice : forall X : FSet A, (X = ∅) + (hexists (fun a => a ∈ X)).
  Proof.
    hinduction.
    - apply (inl idpath).
    - intro a.
      refine (inr (tr (a ; tr idpath))).
    - intros X Y TX TY.
      destruct TX as [XE | HX] ; destruct TY as [YE | HY].
      * refine (inl _).
        rewrite XE, YE.
        apply (union_idem ∅).
      * right.
        strip_truncations.
        destruct HY as [a Ya].
        refine (tr _).
        exists a.
        apply (tr (inr Ya)).
      * right.
        strip_truncations.
        destruct HX as [a Xa].
        refine (tr _).
        exists a.
        apply (tr (inl Xa)).
      * right.
        strip_truncations.
        destruct (HX, HY) as [[a Xa] [b Yb]].
        refine (tr _).
        exists a.
        apply (tr (inl Xa)).
    - solve_mc.
    - solve_mc.
    - solve_mc.
    - solve_mc.
    - solve_mc.
  Defined.
End mere_choice.
