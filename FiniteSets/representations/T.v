(* Type which proves that all types have merely decidable equality implies LEM *)
Require Import HoTT HitTactics Sub.

Module Export T.
  Section HIT.
    Variable A : Type.

    Private Inductive T (B : Type) : Type :=
    | b : T B
    | c : T B.    

    Axiom p : A -> b A = c A.
    Axiom setT : IsHSet (T A).

  End HIT.

  Arguments p {_} _.

  Section T_induction.
    Variable A : Type.
    Variable (P : (T A) -> Type).
    Variable (H : forall x, IsHSet (P x)).
    Variable (bP : P (b A)).
    Variable (cP : P (c A)).
    Variable (pP : forall a : A, (p a) # bP = cP).
    
    (* Induction principle *)
    Fixpoint T_ind
             (x : T A)
             {struct x}
      : P x
      := (match x return _ -> _ -> P x with
          | b => fun _ _ => bP
          | c => fun _ _ => cP                              
          end) pP H.

    Axiom T_ind_beta_p : forall (a : A),
        apD T_ind (p a) = pP a.
  End T_induction.

  Section T_recursion.

    Variable A : Type.
    Variable P : Type.
    Variable H : IsHSet P.
    Variable bP : P.
    Variable cP : P.
    Variable pP : A -> bP = cP.

    Definition T_rec : T A -> P.
    Proof.
      simple refine (T_ind A _ _ _ _ _) ; cbn.
      - apply bP.
      - apply cP.
      - intro a.
        simple refine ((transport_const _ _) @  (pP a)).
    Defined.

    Definition T_rec_beta_p : forall (a : A),
        ap T_rec (p a) = pP a.
    Proof.
      intros.
      unfold T_rec.
      eapply (cancelL (transport_const (p a) _)).
      simple refine ((apD_const _ _)^ @ _).
      apply T_ind_beta_p.
    Defined.
  End T_recursion.

  Instance T_recursion A : HitRecursion (T A)
    := {indTy := _; recTy := _; 
        H_inductor := T_ind A; H_recursor := T_rec A }.

End T.

Section merely_dec_lem.
  Variable A : hProp.
  Context `{Univalence}.

  Definition code_b : T A -> hProp.
  Proof.
    hrecursion.
    - apply Unit_hp.
    - apply A.
    - intro a.
      apply path_iff_hprop.
      * apply (fun _ => a).
      * apply (fun _ => tt).
  Defined.

  Definition code_c : T A -> hProp.
  Proof.
    hrecursion.
    - apply A.
    - apply Unit_hp.
    - intro a.
      apply path_iff_hprop.
      * apply (fun _ => tt).
      * apply (fun _ => a).
  Defined.

  Definition code : T A -> T A -> hProp.
  Proof.
    simple refine (T_rec _ _ _ _ _ _).
    - exact code_b.
    - exact code_c.
    - intro a.
      apply path_forall.
      intro z.
      hinduction z.
      * apply path_iff_hprop.
        ** apply (fun _ => a).
        ** apply (fun _ => tt).
      * apply path_iff_hprop.
        ** apply (fun _ => tt).
        ** apply (fun _ => a).
      * intros. apply set_path2.
  Defined.

  Local Ltac f_prop := apply path_forall ; intro ; apply path_ishprop.

  Lemma transport_code_b_x (a : A) : 
    transport code_b (p a) = fun _ => a.
  Proof.
    f_prop.
  Defined.

  Lemma transport_code_c_x (a : A) : 
    transport code_c (p a) = fun _ => tt.
  Proof.
    f_prop.    
  Defined.

  Lemma transport_code_c_x_V (a : A) : 
    transport code_c (p a)^ = fun _ => a.
  Proof. 
    f_prop.    
  Defined.

  Lemma transport_code_x_b (a : A) : 
    transport (fun x => code x (b A)) (p a) = fun _ => a.
  Proof.
    f_prop.
  Defined.

  Lemma transport_code_x_c (a : A) : 
    transport (fun x => code x (c A)) (p a) = fun _ => tt.
  Proof.
    f_prop.
  Defined.

  Lemma transport_code_x_c_V (a : A) : 
    transport (fun x => code x (c A)) (p a)^ = fun _ => a.
  Proof.
    f_prop.
  Defined.

  Lemma ap_diag {B : Type} {x y : B} (p : x = y) :
    ap (fun x : B => (x, x)) p = path_prod' p p.   
  Proof.
      by path_induction.
  Defined.

  Lemma transport_code_diag (a : A) z :
    (transport (fun i : (T A) => code i i) (p a)) z = tt.
  Proof.
    apply path_ishprop.
  Defined.

  Definition r : forall (x : T A), code x x.
  Proof.
    simple refine (T_ind _ _ _ _ _ _); simpl.
    - exact tt.
    - exact tt.
    - intro a.
      apply transport_code_diag.
  Defined.

  Definition encode_pre : forall (x y : T A), x = y -> code x y
    := fun x y p => transport (fun z => code x z) p (r x).

  Definition encode : forall x y, x = y -> code x y.
  Proof.
    intros x y.
    intro p.
    refine (transport (fun z => code x z) p _). clear p.
    revert x. simple refine (T_ind _ _ _ _ _ _); simpl.
    - exact tt.
    - exact tt.
    - intro a.
      apply path_ishprop.
  Defined.

  Definition decode_b : forall (y : T A), code_b y -> (b A) = y.
  Proof.
    simple refine (T_ind _ _ _ _ _ _) ; simpl.
    - exact (fun _ => idpath).
    - exact (fun a => p a).
    - intro a.
      apply path_forall.
      intro t.
      refine (transport_arrow _ _ _ @ _).
      refine (transport_paths_FlFr _ _ @ _).
      hott_simpl.
      f_ap.
      apply path_ishprop.
  Defined.

  Definition decode_c : forall (y : T A), code_c y -> (c A) = y.
  Proof.
    simple refine (T_ind _ _ _ _ _ _); simpl.
    - exact (fun a => (p a)^).
    - exact (fun _ => idpath).
    - intro a.
      apply path_forall.
      intro t.
      refine (transport_arrow _ _ _ @ _).
      refine (transport_paths_FlFr _ _ @ _).
      rewrite transport_code_c_x_V.
      hott_simpl.      
  Defined.

  Lemma transport_paths_FlFr_trunc :
    forall {X Y : Type} (f g : X -> Y) {x1 x2 : X} (q : x1 = x2)
           (r : f x1 = g x1),
      transport (fun x : X => Trunc 0 (f x = g x)) q (tr r) = tr (((ap f q)^ @ r) @ ap g q).
  Proof.
    destruct q; simpl. intro r.
    refine (ap tr _).
    exact ((concat_1p r)^ @ (concat_p1 (1 @ r))^).
  Defined.
  
  Definition decode : forall (x y : T A), code x y -> x = y.
  Proof.
    simple refine (T_ind _ _ _ _ _ _); simpl.
    - intro y. exact (decode_b y).
    - intro y. exact (decode_c y).
    - intro a.
      apply path_forall. intro z.
      rewrite transport_forall_constant.
      apply path_forall. intros c.
      rewrite transport_arrow.
      hott_simpl.
      rewrite (transport_paths_FlFr _ _).
      revert z c. simple refine (T_ind _ _ _ _ _ _) ; simpl.
      + intro.
        hott_simpl.
        f_ap.
        refine (ap (fun x => (p x)) _).
        apply path_ishprop.
      + intro.        
        rewrite transport_code_x_c_V.
        hott_simpl.
      + intro b.
        apply path_forall.
        intro z.
        rewrite transport_forall.
        apply set_path2.
  Defined.

  Lemma decode_encode (u v : T A) : forall (p : u = v),
      decode u v (encode u v p) = p.
  Proof.
    intros p. induction p.
    simpl. revert u. simple refine (T_ind _ _ _ _ _ _).
    + simpl. reflexivity.
    + simpl. reflexivity.    
    + intro a.
      apply set_path2.
  Defined.

  Lemma encode_decode : forall (u v : T A) (c : code u v),
      encode u v (decode u v c) = c.
  Proof.
    simple refine (T_ind _ _ _ _ _ _).
    - simple refine (T_ind _ _ _ _ _ _).
      + simpl. apply path_ishprop.
      + simpl. intro a. apply path_ishprop.
      + intro a. apply path_forall; intros ?. apply set_path2.
    - simple refine (T_ind _ _ _ _ _ _).
      + simpl. intro a. apply path_ishprop. 
      + simpl. apply path_ishprop. 
      + intro a. apply path_forall; intros ?. apply set_path2.
    - intro a. repeat (apply path_forall; intros ?). apply set_path2.
  Defined.
  

  Instance T_hprop (a : A) : IsHProp (b A = c A).
  Proof.
    apply hprop_allpath.
    intros x y.
    pose (encode (b A) _ x) as t1.
    pose (encode (b A) _ y) as t2.
    assert (t1 = t2).
    {
      unfold t1, t2.
      apply path_ishprop.
    }
    pose (decode _ _ t1) as t3.
    pose (decode _ _ t2) as t4.
    assert (t3 = t4) as H1.
    {
      unfold t3, t4.
      f_ap.
    }
    unfold t3, t4, t1, t2 in H1.
    rewrite ?decode_encode in H1.
    apply H1.
  Defined.
  
  Lemma equiv_pathspace_T : (b A = c A) = A.
  Proof.
    apply path_iff_ishprop.
    - intro x.
      apply (encode (b A) (c A) x).
    - apply p.
  Defined.

End merely_dec_lem.

Theorem merely_dec `{Univalence} : (forall (A : Type) (a b : A), hor (a = b) (~a = b))
                                   ->
                                   forall (A : hProp), A + (~A).
Proof.
  intros.
  specialize (X (T A) (b A) (c A)).
  rewrite (equiv_pathspace_T A) in X.
  strip_truncations.
  apply X.
Defined.
