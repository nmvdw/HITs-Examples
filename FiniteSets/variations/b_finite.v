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
    Variable (P : A -> hProp)
             (n : nat)
             (Xequiv : {a : A & P a } <~> Fin n + Unit).

    Definition split : exists P' : Sub A, exists b : A,
      ({a : A & P' a} <~> Fin n) * (forall x, P x = P' x ∨ merely (x = b)).
    Proof.
      destruct Xequiv as [f [g fg gf adj]].
      unfold Sect in *. 
      pose (fun x : A => sig (fun y : Fin n => x = (g (inl y)).1)) as P'.
      assert (forall x, IsHProp (P' x)).
      {
        intros a. unfold P'.
        apply hprop_allpath.
        intros [x px] [y py].
        simple refine (path_sigma _ _ _ _ _); [ simpl | apply path_ishprop ].
        apply path_sum_inl with Unit.
        cut (g (inl x) = g (inl y)).
        { intros p.
          pose (ap f p) as Hp.
          by rewrite !fg in Hp. }
        apply path_sigma with (px^ @ py).
        apply path_ishprop.
      }
      exists (fun a => BuildhProp (P' a)).
      exists (g (inr tt)).1.
      split.
      { unshelve eapply BuildEquiv.
        { refine (fun x => x.2.1). }
        apply isequiv_biinv.
        unshelve esplit;
          exists (fun x => (((g (inl x)).1; (x; idpath)))).
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
            by rewrite gf.
          + refine (tr (inr (tr _))).
            rewrite Hy.
            by rewrite gf.
        - intros Hstuff.
          strip_truncations.
          destruct Hstuff as [[y Hy] | Ha].
          + rewrite Hy.
            apply (g (inl y)).2.
          + strip_truncations.
            rewrite Ha.
            apply (g (inr tt)).2. }
    Defined.

  End split.
End finite_hott.

Arguments Bfin {_} _.

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
      destruct (split _ P n Hequiv) as
        (P' & b & HP' & HP).
      unfold member, sub_membership.
      rewrite (HP a).
      destruct (IHn P' HP') as [IH | IH].
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
    - destruct (split _ X n FX) as
        (X' & b & FX' & HX).
      pose (X'cow := (X'; Build_Finite _ n (tr FX')) : cow).
      assert ((X; Build_Finite _ (n.+1) (tr FX)) = add_cow b X'cow) as ℵ.
      { simple refine (path_sigma' _ _ _); [ | apply path_ishprop ].
        apply path_forall. intros a.
        unfold X'cow.
        rewrite (HX a). simpl. reflexivity. }
      rewrite ℵ.
      apply koeientaart.
      apply IHn.
  Defined.

  Definition bfin_to_kfin : forall (P : Sub A), Bfin P -> Kf_sub _ P.
  Proof.
    intros P [n f].
    strip_truncations.
    unfold Kf_sub, Kf_sub_intern.
    revert f. revert P.
    induction n; intros P f.
    - exists ∅.
      apply path_forall; intro a; simpl.
      apply path_iff_hprop; [ | contradiction ].
      intros p.
      apply (f (a;p)).
    - destruct (split _ P n f) as
        (P' & b & HP' & HP).
      destruct (IHn P' HP') as [Y HY].
      exists (Y ∪ {|b|}).
      apply path_forall; intro a. simpl.
      rewrite <- HY.
      apply HP.
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
