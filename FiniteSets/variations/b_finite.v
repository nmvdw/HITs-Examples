(* Bishop-finiteness is that "default" notion of finiteness in the HoTT library *)
Require Import HoTT HitTactics.
Require Import Sub notation variations.k_finite.
Require Import fsets.properties.

Section finite_hott.
  Variable (A : Type).
  Context `{Univalence} `{IsHSet A}.

  (* A subobject is B-finite if its extension is B-finite as a type *)
  Definition Bfin (X : Sub A) : hProp := BuildhProp (Finite {a : A & a ∈ X}).

  Global Instance singleton_contr a : Contr {b : A & b ∈ {|a|}}.
  Proof.
    exists (a; tr idpath).
    intros [b p].
    simple refine (Trunc_ind (fun p => (a; tr 1%path) = (b; p)) _ p).
    clear p; intro p. simpl.
    apply path_sigma' with (p^).
    apply path_ishprop.
  Defined.
  
  Definition singleton_fin_equiv' a : Fin 1 -> {b : A & b ∈ {|a|}}.
  Proof.  
    intros _. apply (center {b : A & b ∈ {|a|}}).
  Defined.

  Global Instance singleton_fin_equiv a : IsEquiv (singleton_fin_equiv' a).
  Proof. apply _. Defined.

  Definition singleton : closedSingleton Bfin.
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
    destruct Y as [n Xn].
    strip_truncations.
    destruct Xn as [f [g fg gf adj]].
    destruct n.
    - refine (tr(inl _)).
      apply path_forall. intro z.
      apply path_iff_hprop.
      * intros p.
        contradiction (f (z;p)).
      * contradiction.
    - refine (tr(inr _)).
      apply (tr(g(inr tt))).
  Defined.
  
  Lemma no_union
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

  Section empty.
    Variable (X : A -> hProp)
             (Xequiv : {a : A & a ∈ X} <~> Fin 0).

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
    Variable (X : A -> hProp)
             (n : nat)
             (Xequiv : {a : A & a ∈ X} <~> Fin n + Unit).

    Definition split : {X' : A -> hProp & {a : A & a ∈ X'} <~> Fin n}.
    Proof.
      destruct Xequiv as [f [g fg gf adj]].
      unfold Sect in *. 
      pose (fun x : A => sig (fun y : Fin n => x = (g(inl y)).1 )) as X'.
      assert (forall a : A, IsHProp (X' a)).
      {
        intros.
        unfold X'.
        apply hprop_allpath.
        intros [x px] [y py].
        simple refine (path_sigma _ _ _ _ _).
        * cbn.
          pose (f(g(inl x))) as fgx.
          cut (g(inl x) = g(inl y)).
          {
            intros q.
            pose (ap f q).
            rewrite !fg in p.
            refine (path_sum_inl _ p).
          }
          apply path_sigma with (px^ @ py).
          apply path_ishprop.
        * apply path_ishprop.          
      }
      pose (fun a => BuildhProp(X' a)) as Y.
      exists Y.
      unfold Y, X'.
      cbn.
      unshelve esplit.
      - intros [a [y p]]. apply y.
      - apply isequiv_biinv.
        unshelve esplit.
        * exists (fun x => (( (g(inl x)).1 ;(x;idpath)))).
          unfold Sect.
          intros [a [y p]].
          apply path_sigma with p^.
          simpl.
          rewrite transport_sigma.
          simple refine (path_sigma _ _ _ _ _) ; simpl.
          ** rewrite transport_const ; reflexivity.
          ** apply path_ishprop.
        * exists (fun x => (( (g(inl x)).1 ;(x;idpath)))).
          unfold Sect.
          intros x.
          reflexivity.
    Defined.
    
    Definition new_el : {a' : A & forall z, X z =
                                            lor (split.1 z) (merely (z = a'))}.
    Proof.
      exists ((Xequiv^-1 (inr tt)).1).
      intros.
      apply path_iff_hprop.
      - intros Xz.
        pose (Xequiv (z;Xz)) as fz.
        pose (c := fz).
        assert (c = fz). reflexivity.
        destruct c as [fz1 | fz2].
        * refine (tr(inl _)).
          unfold split ; simpl.
          exists fz1.
          rewrite X0.
          unfold fz.
          destruct Xequiv as [? [? ? sect ?]].
          compute.
          rewrite sect.
          reflexivity.
        * refine (tr(inr(tr _))).
          destruct fz2.
          rewrite X0.
          unfold fz.
          rewrite eissect.
          reflexivity.
      - intros X0.
        strip_truncations.
        destruct X0 as [Xl | Xr].
        * unfold split in Xl ; simpl in Xl.
          destruct Xequiv as [f [g fg gf adj]].
          destruct Xl as [m p].
          rewrite p.
          apply (g (inl m)).2.
        * strip_truncations.
          rewrite Xr.
          apply ((Xequiv^-1(inr tt)).2).
    Defined.

  End split.
End finite_hott.

Arguments Bfin {_} _.

Section Bfin_not_set.
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

  Context `{Univalence}.

  Theorem no_singleton (Hsing : Bfin {|base|}) : Empty.
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

End Bfin_not_set.

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
      pose (new_el _ P n Hequiv) as b.
      destruct b as [b HX'].
      destruct (split _ P n Hequiv) as [X' X'equiv]. simpl in HX'.
      unfold member, sub_membership.
      rewrite (HX' a).
      pose (IHn X' X'equiv) as IH.
      destruct IH as [IH | IH].
      + left. apply (tr (inl IH)).
      + destruct (dec (a = b)) as [Hab | Hab].
        left. apply (tr (inr (tr Hab))).
        right. intros α. strip_truncations.
        destruct α as [β | γ]; [ | strip_truncations]; contradiction.
  Defined.
End dec_membership.

Section cowd.
  Variable (A : Type).
  Context `{DecidablePaths A} `{Univalence}.

  Definition cow := { X : Sub A | Bfin X}.
  Definition empty_cow : cow.
  Proof.
    exists empty. apply empty_finite.
  Defined.

  Definition add_cow : forall a : A, cow -> cow.
  Proof.
    intros a [X PX].
    exists (fun z => lor (X z) (merely (z = a))).
    destruct (dec (a ∈ X)) as [Ha | Ha];
      destruct PX as [n PX];
      strip_truncations.
    - (* a ∈ X *)
      exists n. apply tr.
      transitivity ({a : A & a ∈ X}); [ | apply PX ].
      apply equiv_functor_sigma_id.
      intro a'. eapply equiv_iff_hprop_uncurried ; split; cbn.
      + intros Ha'. strip_truncations.
        destruct Ha' as [HXa' | Haa'].
        * assumption.
        * strip_truncations. rewrite Haa'. assumption.
      + intros HXa'. apply tr.
        left. assumption.
    - (* a ∉ X *)
      exists (S n). apply tr.
      destruct PX as [f [g Hfg Hgf adj]].
      unshelve esplit.
      + intros [a' Ha']. cbn in Ha'.
        destruct (dec (a' = a)) as [Haa' | Haa'].
        * right. apply tt.
        * assert (X a') as HXa'.
          { strip_truncations.
            destruct Ha' as [Ha' | Ha']; [ assumption | ].
            strip_truncations. by (contradiction (Haa' Ha')). }
          apply (inl (f (a';HXa'))).
      + apply isequiv_biinv; simpl.
        unshelve esplit; simpl.
        * unfold Sect; simpl.
          simple refine (_;_).
          { destruct 1 as [M | ?].
            - destruct (g M) as [a' Ha'].
              exists a'. apply tr.
                by left.
            - exists a. apply (tr (inr (tr idpath))). }
          simpl. intros [a' Ha'].
          strip_truncations.
          destruct Ha' as [HXa' | Haa']; simpl;
            destruct (dec (a' = a)); simpl.
          ** apply path_sigma' with p^. apply path_ishprop.
          ** rewrite Hgf; cbn. done.
          ** apply path_sigma' with p^. apply path_ishprop.
          ** rewrite Hgf; cbn. apply path_sigma' with idpath. apply path_ishprop.
        * unfold Sect; simpl.
          simple refine (_;_).
          { destruct 1 as [M | ?].
            - destruct (g M) as [a' Ha'].
              exists a'. apply tr.
                by left.
            - exists a. apply (tr (inr (tr idpath))). }
          simpl. intros [M | [] ].
          ** destruct (dec (_ = a)) as [Haa' | Haa']; simpl.
             { destruct (g M) as [a' Ha']. rewrite Haa' in Ha'. by contradiction. }
             { f_ap. }
          ** destruct (dec (a = a)); try by contradiction.
             reflexivity.
  Defined.

  Theorem cowy
    (P : cow -> hProp)
    (doge : P empty_cow)
    (koeientaart : forall a c, P c -> P (add_cow a c))
    :
    forall X : cow, P X.
  Proof.
    intros [X [n FX]]. strip_truncations.
    revert X FX.
    induction n; intros X FX.
    - pose (HX_emp:= X_empty _ X FX).
      assert ((X; Build_Finite _ 0 (tr FX)) = empty_cow) as HX.
      { apply path_sigma' with HX_emp. apply path_ishprop. }
      rewrite HX. assumption.
    - pose (a' := new_el _ X n FX).
      destruct a' as [a' Ha'].
      destruct (split _ X n FX) as [X' FX'].
      pose (X'cow := (X'; Build_Finite _ n (tr FX')) : cow).
      assert ((X; Build_Finite _ (n.+1) (tr FX)) = add_cow a' X'cow) as ℵ.
      { simple refine (path_sigma' _ _ _); [ | apply path_ishprop ].
        apply path_forall. intros a.
        unfold X'cow.
        specialize (Ha' a). rewrite Ha'. simpl. reflexivity. }
      rewrite ℵ.
      apply koeientaart.
      apply IHn.
  Defined.

  Definition bfin_to_kfin : forall (X : Sub A), Bfin X -> Kf_sub _ X.
  Proof.
    intros X BFinX.
    unfold Bfin in BFinX.
    destruct BFinX as [n iso].
    strip_truncations.
    revert iso ; revert X.
    induction n ; unfold Kf_sub, Kf_sub_intern.
    - intros.
      exists ∅.
      apply path_forall.
      intro z.
      simpl in *.
      apply path_iff_hprop ; try contradiction.
      destruct iso as [f f_equiv].
      apply (fun Xz => f(z;Xz)).
    - intros.
      simpl in *.
      destruct (new_el _ X n iso) as [a HXX'].
      destruct (split _ X n iso) as [X' X'equiv].
      destruct (IHn X' X'equiv) as [Y HY].
      exists (Y ∪ {|a|}).
      unfold map in *.
      apply path_forall.
      intro z.
      rewrite union_isIn.
      rewrite <- (ap (fun h => h z) HY).
      rewrite HXX'.
      cbn.
      reflexivity.
  Defined.

  Lemma kfin_is_bfin : @closedUnion A Bfin.
  Proof.
    intros X Y HX HY.
    pose (Xcow := (X; HX) : cow).
    pose (Ycow := (Y; HY) : cow).
    simple refine (cowy (fun C => Bfin (C.1 ∪ Y)) _ _ Xcow); simpl.
    - assert ((fun a => Trunc (-1) (Empty + Y a)) = (fun a => Y a)) as Help.
      { apply path_forall. intros z; simpl.
        apply path_iff_ishprop.
        + intros; strip_truncations; auto.
          destruct X0; auto. destruct e.
        + intros ?.  apply tr. right; assumption.
          (* TODO FIX THIS with sum_empty_l *)
      }
      rewrite Help. apply HY.
    - intros a [X' HX'] [n FX'Y]. strip_truncations.
      destruct (dec(a ∈ X')) as [HaX' | HaX'].
      * exists n. apply tr.
        transitivity ({a : A & Trunc (-1) (X' a + Y a)}); [| assumption ].
        apply equiv_functor_sigma_id. intro a'.
        apply equiv_iff_hprop.
        { intros Q. strip_truncations.
          destruct Q as [Q | Q].
          - strip_truncations.
            apply tr. left.
            destruct Q ; auto.
            strip_truncations. rewrite t; assumption.
          - apply (tr (inr Q)). }
        { intros Q. strip_truncations.
          destruct Q as [Q | Q]; apply tr.
          - left. apply tr. left. done.
          - right. done. }
      * destruct (dec (a ∈ Y)) as [HaY | HaY ].
        ** exists n. apply tr.
           transitivity ({a : A & Trunc (-1) (X' a + Y a)}); [| assumption ].
           apply equiv_functor_sigma_id. intro a'.
           apply equiv_iff_hprop.
           { intros Q. strip_truncations.
             destruct Q as [Q | Q].
             - strip_truncations.
               apply tr.
               destruct Q.
               left. auto.
               right. strip_truncations. rewrite t; assumption.
             - apply (tr (inr Q)). }
           { intros Q. strip_truncations.
             destruct Q as [Q | Q]; apply tr.
             - left. apply tr. left. done.
             - right. done. }
        ** exists (n.+1). apply tr.
           destruct FX'Y as [f [g Hfg Hgf adj]].
           unshelve esplit.
           { intros [a' Ha']. cbn in Ha'.
             destruct (dec (BuildhProp (a' = a))) as [Ha'a | Ha'a].
             - right. apply tt.
             - left. refine (f (a';_)).
               strip_truncations.
               destruct Ha' as [Ha' | Ha'].
               + strip_truncations.
                 destruct Ha' as [Ha' | Ha'].
                 * apply (tr (inl Ha')).
                 * strip_truncations. contradiction.
               + apply (tr (inr Ha')). }
           { apply isequiv_biinv; simpl.
             unshelve esplit; simpl.
             - unfold Sect; simpl.
               simple refine (_;_).
               { destruct 1 as [M | ?].
                 - destruct (g M) as [a' Ha'].
                   exists a'.
                   strip_truncations; apply tr.
                   destruct Ha' as [Ha' | Ha'].
                   + left. apply (tr (inl Ha')).
                   + right. done.
                 - exists a. apply (tr (inl (tr (inr (tr idpath))))). }
               { intros [a' Ha']; simpl.
                 strip_truncations.
                 destruct Ha' as [HXa' | Haa']; simpl;
                   destruct (dec (a' = a)); simpl.
                 ** apply path_sigma' with p^. apply path_ishprop.
                 ** rewrite Hgf; cbn. apply path_sigma' with idpath. apply path_ishprop.
                 ** apply path_sigma' with p^. apply path_ishprop.
                 ** rewrite Hgf; cbn. done. }
             - unfold Sect; simpl.
               simple refine (_;_).
               { destruct 1 as [M | ?].
                 - (* destruct (g M) as [a' Ha']. *)
                   exists (g M).1.
                   simple refine (Trunc_rec _ (g M).2).
                   intros Ha'.
                   apply tr.
                   (* strip_truncations; apply tr. *)
                   destruct Ha' as [Ha' | Ha'].
                   + left. apply (tr (inl Ha')).
                   + right. done.
                 - exists a. apply (tr (inl (tr (inr (tr idpath))))). }
               simpl. intros [M | [] ].
               ** destruct (dec (_ = a)) as [Haa' | Haa']; simpl.
                  { destruct (g M) as [a' Ha']. simpl in Haa'.
                    strip_truncations.
                    rewrite Haa' in Ha'. destruct Ha'; by contradiction. }
                  { f_ap. transitivity (f (g M)); [ | apply Hfg].
                    f_ap. apply path_sigma' with idpath.
                    apply path_ishprop. }
               ** destruct (dec (a = a)); try by contradiction.
                  reflexivity. }
  Defined.

End cowd.

Section Kf_to_Bf.
  Context `{Univalence}.

  Definition FSet_to_Bfin (A : Type) `{DecidablePaths A} : forall (X : FSet A), Bfin (map X).
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
      apply kfin_is_bfin; auto.
  Defined.

  Instance Kf_to_Bf (X : Type) (Hfin : Kf X) `{DecidablePaths X} : Finite X.
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

End Kf_to_Bf.
