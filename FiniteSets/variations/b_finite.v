(* Bishop-finiteness is that "default" notion of finiteness in the HoTT library *)
Require Import HoTT.
Require Import Sub notation variations.k_finite.
Require Import fsets.properties.

Section finite_hott.
  Variable A : Type.
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
      destruct (new_el X n iso) as [a HXX'].
      destruct (split X n iso) as [X' X'equiv].
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

  Context `{A_deceq : DecidablePaths A}.

(*
  Lemma kfin_is_bfin : closedUnion Bfin.
  Proof.
    intros X Y HX HY.
    unfold Bfin in *.
    destruct HX as [n Xequiv].
    revert X Xequiv.
    induction n.
    - intros.
      strip_truncations.
      rewrite (X_empty X Xequiv).
      assert(∅ ∪ Y = Y).
      { apply path_forall ; intro z.
        compute-[lor].
        eauto with lattice_hints typeclass_instances.
      }      
      rewrite X0.
      apply HY.
    - simpl in *.
      intros.
      destruct HY as [m Yequiv].
      strip_truncations.
      destruct (new_el X n Xequiv) as [a HXX'].
      destruct (split X n Xequiv) as [X' X'equiv].
      destruct (IHn X' (tr X'equiv)) as [k Hk].
      strip_truncations.
      cbn in *.
      rewrite (path_forall _ _ HXX').
      assert
        (forall a0,
          BuildhProp (Trunc (-1) (X' a0 ∨ merely (a0 = a) + Y a0))
          =
          BuildhProp (hor (Trunc (-1) (X' a0 + Y a0)) (merely (a0 = a)))
        ).
      {
        intros.
        apply path_iff_hprop.
        * intros X0.
          strip_truncations.
          destruct X0 as [X0 | X0].
          ** strip_truncations.
             destruct X0 as [X0 | X0].
             *** refine (tr(inl(tr _))).
                 apply (inl X0).
             *** refine (tr(inr X0)).
          ** refine (tr(inl(tr _))).
             apply (inr X0).
        * intros X0.
          strip_truncations.
          destruct X0 as [X0 | X0].
          ** strip_truncations.
             destruct X0 as [X0 | X0].
             *** refine (tr(inl(tr(inl X0)))).
             *** refine (tr(inr X0)).
          ** refine (tr(inl(tr(inr X0)))).            
      }
      (* rewrite (path_forall _ _ X0). *)
      assert
        (
          {a0 : A & hor (Trunc (-1) (X' a0 + Y a0)) (merely (a0 = a))}
          =
          {a0 : A & Trunc (-1) (X' a0 + Y a0)}
          +
          {a0 : A & (merely (a0 = a))}
        ).
      {
        assert ({a0 : A & Trunc (-1) (X' a0 + Y a0)} + {a0 : A & merely (a0 = a)} ->
                {a0 : A & hor (Trunc (-1) (X' a0 + Y a0)) (merely (a0 = a))}).
        {
          intros.
          destruct X1.
          * destruct s as [c p].
            exists c.
            apply tr.
            left.
            apply p.
          * destruct s as [c p].
            exists c.
            apply tr.
            right. apply p.
            
        simple refine (path_universe _).
        * intros [a0 p].
          destruct (dec (a0 = a)).
          ** right. exists a0. apply (tr p0).
          ** left.
             exists a0.
             strip_truncations.
             destruct p ; strip_truncations.
             *** apply (tr t).
             *** contradiction (n0 t).
        * apply isequiv_biinv.
          unfold BiInv.
          split.
          **  
          
          exists a0
      }
      rewrite X1.
      apply finite_sum.
      * simple refine (Build_Finite _ k (tr Hk)).
      * apply singleton.
  Admitted.
  *)
      
End finite_hott.
