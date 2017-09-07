(* Bishop-finiteness is that "default" notion of finiteness in the HoTT library *)
Require Import HoTT HitTactics.
Require Import sub subobjects.k_finite FSets prelude.

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

  Lemma bfin_union : @closedUnion A Bfin.
  Proof.
    intros X Y HX HY.
    destruct HX as [n fX].
    strip_truncations.
    revert fX. revert X.
    induction n; intros X fX.
    - destruct HY as [m fY]. strip_truncations.
      exists m. apply tr.
      transitivity {a : A & a ∈ Y}; [ | assumption ].
      apply equiv_functor_sigma_id.
      intros a.
      apply equiv_iff_hprop.
      * intros Ha. strip_truncations.
        destruct Ha as [Ha | Ha]; [ | apply Ha ].
        contradiction (fX (a;Ha)).
      * intros Ha. apply tr. by right.
    - destruct (split X n fX) as
        (X' & b & HX' & HX).
      assert (Bfin X') by (eexists; apply (tr HX')).
      destruct (dec (b ∈ X')) as [HX'b | HX'b].
      + cut (X ∪ Y = X' ∪ Y).
        { intros HXY. rewrite HXY.
          by apply IHn. }
        apply path_forall. intro a.
        apply path_iff_hprop.
        * intros Ha.
          strip_truncations.
          destruct Ha as [HXa | HYa]; [ | apply tr; by right ].
          rewrite HX in HXa.
          strip_truncations.
          destruct HXa as [HX'a | Hab];
            [ | strip_truncations ]; apply tr; left.
          ** done.
          ** rewrite Hab. apply HX'b.
        * intros Ha.
          strip_truncations. apply tr.
          destruct Ha as [HXa | HYa]; [ left | by right ].
          rewrite HX. apply (tr (inl HXa)).
      + (* b ∉ X' *)
        destruct (IHn X' HX') as [n' fw].
        strip_truncations.
        destruct (dec (b ∈ Y)) as [HYb | HYb].
        { exists n'. apply tr.
          transitivity {a : A & a ∈ X' ∪ Y}; [ | apply fw ].
           apply equiv_functor_sigma_id. intro a.
           apply equiv_iff_hprop; cbn; simple refine (Trunc_rec _).
           { intros [HXa | HYa].
             - rewrite HX in HXa.
               strip_truncations.
               destruct HXa as [HX'a | Hab]; apply tr.
               * by left.
               * right. strip_truncations.
                 rewrite Hab. apply HYb.
             - apply tr. by right. }
           { intros [HX'a | HYa]; apply tr.
             * left. rewrite HX.
               apply (tr (inl HX'a)).
             * by right. } }
        { exists (n'.+1).
          apply tr.
          unshelve eapply BuildEquiv.
          { intros [a Ha]. cbn in Ha.
            destruct (dec (BuildhProp (a = b))) as [Hab | Hab].
            - right. apply tt.
            - left. refine (fw (a;_)).
              strip_truncations. apply tr.
              destruct Ha as [HXa | HYa].
              + left. rewrite HX in HXa.
                strip_truncations.
                destruct HXa as [HX'a | Hab']; [apply HX'a |].
                strip_truncations. contradiction.
              + right. apply HYa. }
          { apply isequiv_biinv.
            unshelve esplit; cbn.
            - unshelve eexists.
              + intros [m | []].
                * destruct (fw^-1 m) as [a Ha].
                  exists a.
                  strip_truncations. apply tr.
                  destruct Ha as [HX'a | HYa]; [ left | by right ].
                  rewrite HX.
                  apply (tr (inl HX'a)).
                * exists b.
                  rewrite HX.
                  apply (tr (inl (tr (inr (tr idpath))))).
              + intros [a Ha]; cbn.
                strip_truncations.
                simple refine (path_sigma' _ _ _); [ | apply path_ishprop ].
                destruct (H a b); cbn.
                * apply p^.
                * rewrite eissect; cbn.
                  reflexivity.
            - unshelve eexists. (* TODO: Duplication!! *)
              + intros [m | []].
                * exists (fw^-1 m).1.
                  simple refine (Trunc_rec _ (fw^-1 m).2).
                  intros [HX'a | HYa]; apply tr; [ left | by right ].
                  rewrite HX.
                  apply (tr (inl HX'a)).
                * exists b.
                  rewrite HX.
                  apply (tr (inl (tr (inr (tr idpath))))).
              + intros [m | []]; cbn.
                destruct (dec (_ = b)) as [Hb | Hb]; cbn.
                { destruct (fw^-1 m) as [a Ha]. simpl in Hb.
                  simple refine (Trunc_rec _ Ha). clear Ha.
                  rewrite Hb.
                  intros [HX'b2 | HYb2]; contradiction. }
                { f_ap. transitivity (fw (fw^-1 m)).
                  - f_ap.
                    apply path_sigma' with idpath.
                    apply path_ishprop.
                  - apply eisretr. }
                destruct (dec (b = b)); [ reflexivity | contradiction ]. } }
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