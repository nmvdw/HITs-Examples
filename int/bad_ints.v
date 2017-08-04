Require Import HoTT.

Module Export BadInts.

  Private Inductive Z : Type :=
  | zero_Z : Z
  | succ : Z -> Z
  | pred : Z -> Z.

  Axiom inv1 : forall n : Z, n = pred(succ n).
  Axiom inv2 : forall n : Z, n = succ(pred n).

  Section Z_induction.
    Variable (P : Z -> Type)
             (a : P zero_Z)
             (s : forall (n : Z), P n -> P (succ n))
             (p : forall (n : Z), P n -> P (pred n))
             (i1 : forall (n : Z) (m : P n), (inv1 n) # m = p (succ n) (s (n) m))
             (i2 : forall (n : Z) (m : P n), (inv2 n) # m = s (pred n) (p (n) m)).

    Fixpoint Z_ind
             (x : Z)
             {struct x}
      : P x
      := 
        (match x return _ -> _ -> P x with
         | zero_Z => fun _ => fun _ => a
         | succ n => fun _ => fun _ => s n (Z_ind n)
         | pred n => fun _ => fun _ => p n (Z_ind n)
         end) i1 i2.

    Axiom Z_ind_beta_inv1 : forall (n : Z), apD Z_ind (inv1 n) = i1 n (Z_ind n).

    Axiom Z_ind_beta_inv2 : forall (n : Z), apD Z_ind (inv2 n) = i2 n (Z_ind n).
  End Z_induction.

  Section Z_recursion.
    Context  {P : Type}.
    Variable  (a : P)
              (s : P -> P)
              (p : P -> P)
              (i1 : forall (m : P), m = p(s m))
              (i2 : forall (m : P), m = s(p m)).

    Definition Z_rec : Z -> P.
    Proof.
      simple refine (Z_ind _ _ _ _ _ _) ; simpl.
      - apply a.
      - intro ; apply s.
      - intro ; apply p.
      - intros.
        refine (transport_const _ _ @ (i1 _)).
      - intros.
        refine (transport_const _ _ @ (i2 _)).
    Defined.
    
    Definition Z_rec_beta_inv1 (n : Z) : ap Z_rec (inv1 n) = i1 (Z_rec n).
    Proof.
      unfold Z_rec.
      eapply (cancelL (transport_const (inv1 n) _)).
      simple refine ((apD_const _ _)^ @ _).
      apply Z_ind_beta_inv1.
    Defined.

    Definition Z_rec_beta_inv2 (n : Z) : ap Z_rec (inv2 n) = i2 (Z_rec n).
    Proof.
      unfold Z_rec.
      eapply (cancelL (transport_const (inv2 n) _)).
      simple refine ((apD_const _ _)^ @ _).
      apply Z_ind_beta_inv2.
    Defined.

  End Z_recursion.
  
End BadInts.

Section NotSet.
  Context `{Univalence}.

  Definition Z_to_S : Z -> S1.
  Proof.
    refine (Z_rec base idmap idmap (fun _ => idpath) _).
    simple refine (S1_ind _ _ _).
    - apply loop.
    - refine (transport_paths_FlFr _ _ @ _).
      refine (ap (fun z => _ @ z) (ap_idmap _) @ _).
      refine (ap (fun z => (z^ @ loop) @ loop) (ap_idmap _) @ _).
      apply (ap (fun z => z @ loop) (concat_Vp loop) @ concat_1p loop).
  Defined.

  Definition p1 : pred (succ (pred zero_Z)) = pred (succ (pred (succ (pred zero_Z))))
    := inv1 (pred (succ (pred zero_Z))).

  Lemma q1 : ap Z_to_S p1  = reflexivity base.
  Proof.
    apply Z_rec_beta_inv1.
  Defined.

  Definition p2 : pred (succ (pred zero_Z)) = pred (succ (pred (succ (pred zero_Z))))
    := ap pred (inv2 (succ (pred zero_Z))).

  Lemma q2 : ap Z_to_S p2 = loop.
  Proof.
    refine ((ap_compose _ _ _)^ @ _).
    assert (forall (n m : Z) (p : n = m), ap (fun n : Z => Z_to_S(pred n)) p = ap Z_to_S p) as X.
    { reflexivity. }
    refine (X _ _ _ @ _).
    unfold Z_to_S.
    refine (Z_rec_beta_inv2 _ _ _ _ _ (succ (pred zero_Z))).
  Defined.

  Lemma ZSet_loop_refl (ZSet : IsHSet Z) : idpath = loop.
  Proof.
    assert (ap Z_to_S p1 = ap Z_to_S p2).
    {
      assert (p1 = p2). { apply (ZSet _ _ p1 p2). }
      apply (ap (fun z => ap Z_to_S z) X).
    }
    apply (q1^ @ X @ q2).
  Defined.

  Lemma ZSet_not_hset (ZSet : IsHSet Z) : False.
  Proof.
    enough (idpath = loop). 
    - assert (S1_encode _ idpath = S1_encode _ (loopexp loop (pos Int.one))) as H' by f_ap.
      rewrite S1_encode_loopexp in H'. simpl in H'. symmetry in H'.
      apply (pos_neq_zero H').
    - apply ZSet_loop_refl.
      apply ZSet.
  Qed.
End NotSet.