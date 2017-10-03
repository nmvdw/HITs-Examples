(* Bishop-finiteness is that "default" notion of finiteness in the HoTT library *)
Require Import HoTT HitTactics.
Require Import FSets interfaces.lattice_interface.
From subobjects Require Import sub k_finite.

Section finite_hott.
  Variable (A : Type).
  Context `{Univalence}.

  (* A subobject is B-finite if its extension is B-finite as a type *)
  Definition Bfin (X : Sub A) : hProp := BuildhProp (Finite {a : A & a ∈ X}).

  Global Instance singleton_contr a `{IsHSet A} : Contr {b : A & b ∈ {|a|}}.
  Proof.
    exists (a; tr idpath).
    intros [b p].
    simple refine (Trunc_ind (fun p => (a; tr 1%path) = (b; p)) _ p).
    clear p; intro p. simpl.
    apply path_sigma_hprop; simpl.
    apply p^.
  Defined.
  
  Definition singleton_fin_equiv' a : Fin 1 -> {b : A & b ∈ {|a|}}.
  Proof.  
    intros _. apply (a; tr idpath).
  Defined.

  Global Instance singleton_fin_equiv a `{IsHSet A} : IsEquiv (singleton_fin_equiv' a).
  Proof. apply _. Defined.

  Definition singleton `{IsHSet A} : closedSingleton Bfin.
  Proof.
    intros a.
    simple refine (Build_Finite _ 1 _).
    apply tr.    
    symmetry.
    refine (BuildEquiv _ _ (singleton_fin_equiv' a) _).
  Defined.

  Definition empty_finite : closedEmpty Bfin.
  Proof.
    simple refine (Build_Finite _ 0 _).
    apply tr.
    simple refine (BuildEquiv _ _ _ _).
    intros [a p]; apply p.
  Defined.

  Definition decidable_empty_finite : hasDecidableEmpty Bfin.
  Proof.
    intros X Y.
    destruct Y as [n f].
    strip_truncations.
    destruct n.
    - refine (tr(inl _)).
      apply path_forall. intro z.
      apply path_iff_hprop.
      * intros p.
        contradiction (f (z;p)).
      * contradiction.
    - refine (tr(inr _)).
      apply (tr(f^-1(inr tt))).
  Defined.
  
  Lemma no_union `{IsHSet A}
        (f : forall (X Y : Sub A),
            Bfin X -> Bfin Y -> Bfin (X ∪ Y))
        (a b : A) :
      hor (a = b) (a = b -> Empty).
  Proof.
    specialize (f {|a|} {|b|} (singleton a) (singleton b)).
    unfold Bfin in f.
    destruct f as [n pn].
    strip_truncations.
    destruct pn as [f [g fg gf _]].
    destruct n as [|n].
    unfold Sect in *.
    - contradiction f.
      exists a. apply (tr(inl(tr idpath))).
    - destruct n as [|n].
      + (* If the size of the union is 1, then (a = b) *)
        refine (tr (inl _)).
        pose (s1 := (a;tr(inl(tr idpath)))
               : {c : A & Trunc (-1) (Trunc (-1) (c = a) + Trunc (-1) (c = b))}).
        pose (s2 := (b;tr(inr(tr idpath)))
               : {c : A & Trunc (-1) (Trunc (-1) (c = a) + Trunc (-1) (c = b))}).
        refine (ap (fun x => x.1) (gf s1)^ @ _ @ (ap (fun x => x.1) (gf s2))).
        assert (fs_eq : f s1 = f s2).
        { by apply path_ishprop. }
        refine (ap (fun x => (g x).1) fs_eq).
      + (* Otherwise, ¬(a = b) *)
        refine (tr (inr _)).
        intros p.
        pose (s1 := inl (inr tt) : Fin n + Unit + Unit).
        pose (s2 := inr tt : Fin n + Unit + Unit).
        pose (gs1 := g s1).
        pose (c := g s1).
        pose (gs2 := g s2).
        pose (d := g s2).
        assert (Hgs1 : gs1 = c) by reflexivity.
        assert (Hgs2 : gs2 = d) by reflexivity.
        destruct c as [x px'].
        destruct d as [y py'].        
        simple refine (Trunc_ind _ _ px') ; intros px.
        simple refine (Trunc_ind _ _ py') ; intros py.
        simpl.
        cut (x = y).
        {
          enough (s1 = s2) as X.
          {
            intros. 
            unfold s1, s2 in X.
            refine (not_is_inl_and_inr' (inl(inr tt)) _ _).
            + apply tt.
            + rewrite X ; apply tt.
          }
          transitivity (f gs1).
          { apply (fg s1)^. }
          symmetry ; transitivity (f gs2).
          { apply (fg s2)^. }
          rewrite Hgs1, Hgs2.
          f_ap.
          simple refine (path_sigma _ _ _ _ _); [ | apply path_ishprop ]; simpl.
          destruct px as [p1 | p1] ; destruct py as [p2 | p2] ; strip_truncations.
          * apply (p2 @ p1^).
          * refine (p2 @ _^ @ p1^). auto.
          * refine (p2 @ _ @ p1^). auto.
          * apply (p2 @ p1^).
        }
        destruct px as [px | px] ; destruct py as [py | py]; strip_truncations.
        ** apply (px @ py^).
        ** refine (px @ _ @ py^). auto.
        ** refine (px @ _ @ py^). symmetry. auto.
        ** apply (px @ py^).
  Defined.      
End finite_hott.

Section singleton_set.
  Variable (A : Type).
  Context `{Univalence}.

  Definition el x : {b : A & b ∈ {|x|}} := (x;tr idpath).
  
  Theorem single_bfin_set (HA : forall a, {b : A & b ∈ {|a|}} <~> Fin 1)
    : forall (x : A) (p : x = x), p = idpath.
  Proof.
    intros x p.
    specialize (HA x).
    pose (el x) as X.
    pose (ap HA^-1 (ap HA (path_sigma _ X X p (path_ishprop _ _)))) as q.
    assert (p = ap (fun z => z.1) ((eissect HA X)^ @ q @ eissect HA X)) as H1.
    {
      unfold q.
      rewrite <- ap_compose.
      enough(forall r,
                (eissect HA X)^
                @ ap (fun x0 : {b : A & b ∈ {|x|}} => HA^-1 (HA x0)) r
                  @ eissect HA X = r
            ) as H2.
      {
        rewrite H2.
        refine (@pr1_path_sigma _ _ X X p _)^.
      }
      induction r.
      hott_simpl.
    }
    assert (idpath = ap (fun z => z.1) ((eissect HA X)^ @ idpath @ eissect HA X)) as H2.
    { hott_simpl. }
    rewrite H1, H2.
    repeat f_ap.
    unfold q.
    enough (ap HA (path_sigma (fun b : A => b ∈ {|x|}) X X p (path_ishprop _ _)) = idpath) as H3.
    {
      rewrite H3.
      reflexivity.
    }
    apply path_ishprop.
  Defined.
End singleton_set.

Section empty.
  Variable (A : Type).
  Variable (X : A -> hProp)
           (Xequiv : {a : A & a ∈ X} <~> Fin 0).
  Context `{Univalence}.
  Lemma X_empty : X = ∅.
  Proof.
    apply path_forall.
    intro z.
    apply path_iff_hprop ; try contradiction.
    intro x.
    destruct Xequiv as [f fequiv].
    contradiction (f(z;x)).
  Defined.  
End empty.

Section split.
  Context `{Univalence}.
  Variable (A : Type).
  Variable (P : A -> hProp)
           (n : nat)
           (f : {a : A & P a } <~> Fin n + Unit).

  Definition split : exists P' : Sub A, exists b : A,
        ({a : A & P' a} <~> Fin n) * (forall x, P x = (P' x ∨ merely (x = b))).
  Proof.
    pose (fun x : A => sig (fun y : Fin n => x = (f^-1 (inl y)).1)) as P'.
    assert (forall x, IsHProp (P' x)).
    {
      intros a. unfold P'.
      apply hprop_allpath.
      intros [x px] [y py].
      pose (p := px^ @ py).
      assert (p2 : p # (f^-1 (inl x)).2 = (f^-1 (inl y)).2).
      { apply path_ishprop. }
      simple refine (path_sigma' _ _ _).
      - apply path_sum_inl with Unit.
        refine (transport (fun z => z = inl y) (eisretr f (inl x)) _).
        refine (transport (fun z => _ = z) (eisretr f (inl y)) _).
        apply (ap f).
        apply path_sigma_hprop. apply p.
      - rewrite transport_paths_FlFr.
        hott_simpl; cbn.
        rewrite ap_compose.
        rewrite (ap_compose inl f^-1).
        rewrite ap_inl_path_sum_inl.
        repeat (rewrite transport_paths_FlFr; hott_simpl).
        rewrite !ap_pp.
        rewrite ap_V.
        rewrite <- !other_adj.
        rewrite <- (ap_compose f (f^-1)).
        rewrite ap_equiv.
        rewrite !ap_pp.
        rewrite ap_pr1_path_sigma_hprop.
        rewrite !concat_pp_p.
        rewrite !ap_V.
        rewrite concat_Vp.
        rewrite (concat_p_pp (ap pr1 (eissect f (f^-1 (inl x))))^).
        rewrite concat_Vp.
        hott_simpl. }
    exists (fun a => BuildhProp (P' a)).
    exists (f^-1 (inr tt)).1.
    split.
    { unshelve eapply BuildEquiv.
      { refine (fun x => x.2.1). }
      apply isequiv_biinv.
      unshelve esplit;
        exists (fun x => (((f^-1 (inl x)).1; (x; idpath)))).
      - intros [a [y p]]; cbn.
        eapply path_sigma with p^.
        apply path_ishprop.
      - intros x; cbn.
        reflexivity. }
    { intros a.
      unfold P'.
      apply path_iff_hprop.
      - intros Ha.
        pose (y := f (a;Ha)).
        assert (Hy : y = f (a; Ha)) by reflexivity.
        destruct y as [y | []].
        + refine (tr (inl _)).
          exists y.
          rewrite Hy.
          by rewrite eissect.
        + refine (tr (inr (tr _))).
          rewrite Hy.
          by rewrite eissect.
      - intros Hstuff.
        strip_truncations.
        destruct Hstuff as [[y Hy] | Ha].
        + rewrite Hy.
          apply (f^-1 (inl y)).2.
        + strip_truncations.
          rewrite Ha.
          apply (f^-1 (inr tt)).2. }
  Defined.
End split.

Arguments Bfin {_} _.
Arguments split {_} {_} _ _ _.

Section Bfin_no_singletons.
  Definition S1toSig (x : S1) : {x : S1 & merely(x = base)}.
  Proof.
    exists x.
    simple refine (S1_ind (fun z => merely(z = base)) _ _ x) ; simpl.
    - apply (tr idpath).
    - apply path_ishprop.
  Defined.

  Instance S1toSig_equiv : IsEquiv S1toSig.
  Proof.
    apply isequiv_biinv.
    split.
    - exists (fun x => x.1).
      simple refine (S1_ind _ _ _) ; simpl.
      * reflexivity.
      * rewrite transport_paths_FlFr.
        hott_simpl.
    - exists (fun x => x.1).
      intros [z x].
      simple refine (path_sigma _ _ _ _ _) ; simpl.
      * reflexivity.
      * apply path_ishprop.
  Defined.

  Theorem no_singleton `{Univalence} (Hsing : Bfin {|base|}) : Empty.
  Proof.
    destruct Hsing as [n equiv].
    strip_truncations.
    assert (S1 <~> Fin n) as X.
    { apply (equiv_compose equiv S1toSig). }
    assert (IsHSet S1) as X1.
    {
      rewrite (path_universe X).
      apply _.
    }
    enough (idpath = loop). 
    - assert (S1_encode _ idpath = S1_encode _ (loopexp loop (pos Int.one))) as H' by f_ap.
      rewrite S1_encode_loopexp in H'. simpl in H'. symmetry in H'.
      apply (pos_neq_zero H').
    - apply set_path2.
  Defined.
End Bfin_no_singletons.

(* If A has decidable equality, then every Bfin subobject has decidable membership *)
Section dec_membership.
  Variable (A : Type).
  Context `{DecidablePaths A} `{Univalence}.
  Global Instance DecidableMembership (P : Sub A) (Hfin : Bfin P) (a : A) :
    Decidable (a ∈ P).
  Proof.
    destruct Hfin as [n Hequiv].
    strip_truncations.
    revert Hequiv.
    revert P.
    induction n.
    - intros.
      pose (X_empty _ P Hequiv) as p.
      rewrite p.
      apply _.
    - intros.
      destruct (split P n Hequiv) as
        (P' & b & HP' & HP).
      unfold member, sub_membership.
      rewrite (HP a).
      destruct (IHn P' HP') as [IH | IH].
      + left. apply (tr (inl IH)).
      + destruct (dec (a = b)) as [Hab | Hab].
        left. apply (tr (inr (tr Hab))).
        right. intros α. strip_truncations.
        destruct α as [? | ?]; [ | strip_truncations]; contradiction.
  Defined.
End dec_membership.

Section bfin_kfin.
  Context `{Univalence}.
  Lemma bfin_to_kfin : forall (B : Type), Finite B -> Kf B.
  Proof.
    apply finite_ind_hprop.
    - intros. apply _.
    - apply Kf_unfold.
      exists ∅. intros [].
    - intros B [n f] IH.
      strip_truncations.
      apply Kf_unfold in IH.
      destruct IH as [X HX].
      apply Kf_unfold.
      exists ((fmap FSet inl X) ∪ {|inr tt|}); simpl.
      intros [a | []]; apply tr.
      + left.
        apply fmap_isIn.
        apply (HX a).
      + right. apply (tr idpath).
  Defined.

  Definition bfin_to_kfin_sub A : forall (P : Sub A), Bfin P -> Kf_sub _ P.
  Proof.
    intros P [n f].
    strip_truncations.
    revert f. revert P.
    induction n; intros P f.
    - exists ∅.
      apply path_forall; intro a; simpl.
      apply path_iff_hprop; [ | contradiction ].
      intros p.
      apply (f (a;p)).
    - destruct (split P n f) as
        (P' & b & HP' & HP).
      destruct (IHn P' HP') as [Y HY].
      exists (Y ∪ {|b|}).
      apply path_forall; intro a. simpl.
      rewrite <- HY.
      apply HP.
  Defined.
End bfin_kfin.

Section kfin_bfin.
  Variable (A : Type).
  Context `{DecidablePaths A} `{Univalence}.

  Lemma notIn_ext_union_singleton (b : A) (Y : Sub A) :
    ~ (b ∈ Y) ->
    {a : A & a ∈ ({|b|} ∪ Y)} <~> {a : A & a ∈ Y} + Unit.
  Proof.
    intros HYb.
    unshelve eapply BuildEquiv.
    { intros [a Ha]. cbn in Ha.
      destruct (dec (BuildhProp (a = b))) as [Hab | Hab].
      - right. apply tt.
      - left. exists a.
        strip_truncations.
        destruct Ha as [HXa | HYa].
        + refine (Empty_rec _).
          strip_truncations.
          by apply Hab.
        + apply HYa. }
    { apply isequiv_biinv.
      unshelve esplit; cbn.
      - unshelve eexists.
        + intros [[a Ha] | []].
          * exists a.
            apply tr.
            right. apply Ha.
          * exists b.
            apply (tr (inl (tr idpath))).
        + intros [a Ha]; cbn.
          strip_truncations.
          simple refine (path_sigma' _ _ _); [ | apply path_ishprop ].
          destruct (H a b); cbn.
          * apply p^.
          * reflexivity.
      - unshelve eexists. (* TODO ACHTUNG CODE DUPLICATION *)
        + intros [[a Ha] | []].
          * exists a.
            apply tr.
            right. apply Ha.
          * exists b.
            apply (tr (inl (tr idpath))).
        + intros [[a Ha] | []]; cbn.
          destruct (dec (_ = b)) as [Hb | Hb]; cbn.
          { refine (Empty_rec _).
            rewrite Hb in Ha.
            contradiction. }            
          { reflexivity. }
          destruct (dec (b = b)); [ reflexivity | contradiction ]. }
  Defined.    

  Theorem bfin_union : @closedUnion A Bfin.
  Proof.
    intros X Y HX HY.
    destruct HX as [n fX].
    strip_truncations.
    revert fX. revert X.
    induction n; intros X fX.
    - rewrite (X_empty _ X fX).
      rewrite (neutralL_max (Sub A)).
      apply HY.
    - destruct (split X n fX) as
        (X' & b & HX' & HX).
      assert (Bfin (X'∪ Y)) by (by apply IHn).
      destruct (dec (b ∈ (X' ∪ Y))) as [HX'Yb | HX'Yb].
      + cut (X ∪ Y = X' ∪ Y).
        { intros HXY. rewrite HXY. assumption. }
        apply path_forall. intro a.
        unfold union, sub_union, max_fun.
        rewrite HX.
        rewrite (commutativity (X' a)).
        rewrite (associativity _ (X' a)).
        apply path_iff_hprop.
        * intros Ha.
          strip_truncations.
          destruct Ha as [HXa | HYa]; [ | assumption ].
          strip_truncations.
          rewrite HXa.
          by apply tr.
        * intros Ha.
          apply (tr (inr Ha)).
      + destruct (IHn X' HX') as [n' fw].
        strip_truncations.
        exists (n'.+1).
        apply tr.
        transitivity ({a : A & a ∈ (fun a => merely (a = b)) ∪ (X' ∪ Y)}).
        { apply equiv_functor_sigma_id.
          intro a.
          rewrite <- (associative_max (Sub A)).
          assert (X = X' ∪ (fun a => merely (a = b))) as HX_.
          { apply path_forall. intros ?.
            unfold union, sub_union, max_fun.
            apply HX. }
          rewrite HX_.
          rewrite <- (commutative_max (Sub A) X').
          reflexivity. }
        cbn[Fin].
        etransitivity. apply (notIn_ext_union_singleton b _ HX'Yb).
        by rewrite ((equiv_path _ _)^-1 fw).
  Defined.

  Definition FSet_to_Bfin : forall (X : FSet A), Bfin (map X).
  Proof.
    hinduction; try (intros; apply path_ishprop).
    - exists 0. apply tr. simpl.
      simple refine (BuildEquiv _ _ _ _).
      destruct 1 as [? []].
    - intros a.
      exists 1. apply tr. simpl.
      transitivity Unit; [ | symmetry; apply sum_empty_l ].
      unshelve esplit.
      + exact (fun _ => tt).
      + apply isequiv_biinv. split.
        * exists (fun _ => (a; tr(idpath))).
          intros [b Hb]. strip_truncations.
          apply path_sigma' with Hb^.
          apply path_ishprop.
        * exists (fun _ => (a; tr(idpath))).
          intros []. reflexivity.
    - intros Y1 Y2 HY1 HY2.
      apply bfin_union; auto.
  Defined.

End kfin_bfin.

Instance Kf_to_Bf (X : Type) `{Univalence} `{DecidablePaths X} (Hfin : Kf X) : Finite X.
Proof.
  apply Kf_unfold in Hfin.
  destruct Hfin as [Y HY].
  pose (X' := FSet_to_Bfin _ Y).
  unfold Bfin in X'.
  simple refine (finite_equiv' _ _ X').
  unshelve esplit.
  - intros [a ?]. apply a.
  - apply isequiv_biinv. split.
    * exists (fun a => (a;HY a)).
      intros [b Hb].
      apply path_sigma' with idpath.
      apply path_ishprop.
    * exists (fun a => (a;HY a)).
      intros b. reflexivity.
Defined.