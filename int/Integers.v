Require Import HoTT HitTactics.
From HoTTClasses Require Import interfaces.abstract_algebra tactics.ring_tac theory.rings.

Module Export Ints.

  Private Inductive Z : Type :=
  | zero_Z : Z
  | succ : Z -> Z
  | pred : Z -> Z.

  Axiom inv1 : forall n : Z, n = pred(succ n).
  Axiom inv2 : forall n : Z, n = succ(pred n).
  Axiom ZisSet : IsHSet Z.

  Section Z_induction.
    Variable (P : Z -> Type)
             (H : forall n, IsHSet (P n))
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
        (match x return _ -> _ -> _ -> P x with
         | zero_Z => fun _ _ _ => a
         | succ n => fun _ _ _ => s n (Z_ind n)
         | pred n => fun _ _ _ => p n (Z_ind n)
         end) i1 i2 H.

    Axiom Z_ind_beta_inv1 : forall (n : Z), apD Z_ind (inv1 n) = i1 n (Z_ind n).

    Axiom Z_ind_beta_inv2 : forall (n : Z), apD Z_ind (inv2 n) = i2 n (Z_ind n).
  End Z_induction.

  Section Z_recursion.
    Variable  (P : Type)
              (H : IsHSet P)
              (a : P)
              (s : P -> P)
              (p : P -> P)
              (i1 : forall (m : P), m = p(s m))
              (i2 : forall (m : P), m = s(p m)).

    Definition Z_rec : Z -> P.
    Proof.
      simple refine (Z_ind _ _ _ _ _ _ _) ; simpl.
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

  Instance Z_recursion : HitRecursion Z :=
    {
      indTy := _; recTy := _; 
      H_inductor := Z_ind; H_recursor := Z_rec }.
End Ints.

Section ring_Z.
  Fixpoint nat_to_Z (n : nat) : Z := 
    match n with
    | 0 => zero_Z
    | S m => succ (nat_to_Z m)
    end.

  Definition plus : Z -> Z -> Z := fun x => Z_rec Z _ x succ pred inv1 inv2.

  Lemma plus_0n : forall x, plus zero_Z x = x.
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - reflexivity.
    - intros y Hy.
      apply (ap succ Hy).
    - intros y Hy.
      apply (ap pred Hy).
  Defined.

  Definition plus_n0 x :  plus x zero_Z = x := idpath x.

  Lemma plus_Sn x : forall y, plus (succ x) y = succ(plus x y).
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - reflexivity.
    - intros y Hy.
      apply (ap succ Hy).
    - intros y Hy.
      apply (ap pred Hy @ (inv1 (plus x y))^ @ inv2 (plus x y)).
  Defined.

  Definition plus_nS x y : plus x (succ y) = succ(plus x y) := idpath.

  Lemma plus_Pn x : forall y, plus (pred x) y = pred (plus x y).
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - reflexivity.
    - intros y Hy.
      apply (ap succ Hy @ (inv2 (plus x y))^ @ inv1 (plus x y)).
    - intros y Hy.
      apply (ap pred Hy).
  Defined.

  Definition plus_nP x y : plus x (pred y) = pred(plus x y) := idpath.      

  Lemma plus_comm x : forall y : Z, plus x y = plus y x.
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - apply (plus_0n x)^.
    - intros n H1.
      apply (ap succ H1 @ (plus_Sn _ _)^).
    - intros n H1.
      apply (ap pred H1 @ (plus_Pn _ _)^).
  Defined.

  Lemma plus_assoc x y : forall z : Z, plus (plus x y) z = plus x (plus y z).
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - reflexivity.
    - intros Sz HSz.
      refine (ap succ HSz).
    - intros Pz HPz.
      apply (ap pred HPz).
  Defined.

  Definition negate : Z -> Z := Z_rec Z _ zero_Z pred succ inv2 inv1.

  Lemma negate_negate : forall x, negate(negate x) = x.
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - reflexivity.
    - intros Sy HSy.
      apply (ap succ HSy).
    - intros Py HPy.
      apply (ap pred HPy).
  Defined.

  Definition minus x y : Z := plus x (negate y).

  Lemma plus_negatex : forall x, plus x (negate x) = zero_Z.
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - reflexivity.
    - intros Sx HSx.
      refine (ap pred (plus_Sn _ _) @ _).
      refine ((inv1 _)^ @ HSx).
    - intros Px HPx.
      refine (ap succ (plus_Pn _ _) @ _).
      refine ((inv2 _)^ @ HPx).
  Defined.

  Definition plus_xnegate x : plus (negate x) x = zero_Z :=
    plus_comm (negate x) x @ plus_negatex x.

  Lemma plus_negate x : forall y, plus (negate x) (negate y) = negate (plus x y).
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - reflexivity.
    - intros Sy HSy.
      apply (ap pred HSy).
    - intros Py HPy.
      apply (ap succ HPy).
  Defined.
  
  Definition times (x : Z) : Z -> Z.
  Proof.
    hrecursion.
    - apply zero_Z.
    - apply (plus x).
    - apply (fun z => minus z x).
    - intros ; unfold minus.
      symmetry.
      refine (ap (fun z => plus z (negate x)) (plus_comm x m) @ _).
      refine (plus_assoc _ _ _ @ _).
      refine (ap (fun z => plus m z) (plus_negatex _) @ _).
      apply plus_n0.
    - intros ; unfold minus.
      symmetry.
      refine (ap (fun z => plus x z) (plus_comm _ _) @ _).
      refine ((plus_assoc _ _ _)^ @ _).
      refine (ap (fun z => plus z m) (plus_negatex _) @ _).
      apply plus_0n.    
  Defined.

  Lemma times_0n : forall x, times zero_Z x = zero_Z.
  Proof.
     hinduction ; try (intros ; apply set_path2) ; simpl.
    - reflexivity.
    - intros Sx HSx.
      apply (plus_0n _ @ HSx).
    - intros Px HPx.
      unfold minus ; simpl ; apply HPx.
  Defined.

  Definition times_n0 n : times n zero_Z = zero_Z := idpath.

  Lemma times_Sn x : forall y, times (succ x) y = plus y (times x y).
  Proof.
    hinduction ; try (intros ; apply set_path2) ; simpl.
    - reflexivity.
    - intros Sy HSy.
      refine (ap (fun z => plus (succ x) z) HSy @ _).
      refine (plus_Sn _ _ @ _).
      refine (_ @ (plus_Sn _ _)^).
      refine (ap succ _).
      refine ((plus_assoc _ _ _)^ @ _).
      refine (_ @ plus_assoc _ _ _).
      refine (ap (fun z => plus z (times x Sy)) (plus_comm _ _)).
    - intros Py HPy ; unfold minus.
      refine (ap (fun z => plus z (negate (succ x))) HPy @ _) ; simpl.
      refine (_ @ (plus_Pn _ _)^).
      refine (ap pred _).
      apply plus_assoc.
  Defined.

  Definition times_nS x y : times x (succ y) = plus x (times x y) := idpath.

  Lemma times_1n x : times (succ zero_Z) x = x.
  Proof.
    refine (times_Sn _ _ @ _).
    refine (ap (plus x) (times_0n _) @ (plus_n0 x)).
  Defined.    

  Lemma times_Pn x : forall y, times (pred x) y = minus (times x y) y.
  Proof.
    hinduction ; try (intros ; apply set_path2) ; simpl.
    - reflexivity.
    - intros Sy HSy.
      refine (ap (fun z => plus (pred x) z) HSy @ _) ; unfold minus.
      refine (plus_Pn _ _ @ _) ; simpl.
      refine (ap pred _).
      apply (plus_assoc _ _ _)^.
    - intros Py HPy.
      refine (ap (fun z => minus z (pred x)) HPy @ _) ; unfold minus ; simpl.
      refine (ap succ _).
      refine (plus_assoc _ _ _ @ _).
      refine (_ @ (plus_assoc _ _ _)^).
      refine (ap (fun z => plus (times x Py) z) (plus_comm _ _)).
  Defined.

  Definition times_nP x y : times x (pred y) = minus (times x y) x := idpath.

  Lemma times_comm x : forall y, times x y = times y x.
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - apply (times_0n x)^.
    - intros Sx HSx.
      apply (ap (fun z => plus x z) HSx @ (times_Sn _ _)^).
    - intros Py HPy.
      apply (ap (fun z => minus z x) HPy @ (times_Pn _ _)^).
  Defined.

  Lemma times_negatex x : forall y, times x (negate y) = negate (times x y).
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - reflexivity.
    - intros Sy HSy.
      unfold minus.
      refine (ap (fun z => plus z (negate x)) HSy @ _).
      refine (plus_negate _ _ @ _).
      apply (ap negate (plus_comm _ _)).
    - intros Py HPy.
      refine (ap (plus x) HPy @ _).
      unfold minus.
      refine (ap (fun z => plus z (negate (times x Py))) (negate_negate _)^ @ _).
      refine (plus_negate _ _ @ _).
      refine (ap negate (plus_comm _ _)).
  Defined.     
  
  Definition times_xnegate x y : times (negate x) y = negate (times x y) :=
    times_comm (negate x) y @ times_negatex y x @ ap negate (times_comm y x).

  Lemma dist_times_plus x y : forall z, times x (plus y z) = plus (times x y) (times x z).
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - reflexivity.
    - intros Sz HSz.
      refine (ap (plus x) HSz @ _).
      refine ((plus_assoc _ _ _)^ @ _).
      refine (_ @ plus_assoc _ _ _).
      refine (ap (fun z => plus z (times x Sz)) (plus_comm _ _)).
    - intros Pz HPz.
      refine (ap (fun z => minus z x) HPz @ _).
      unfold minus ; simpl.
      apply plus_assoc.
  Defined.

  Lemma dist_plus_times x y z : times (plus x y) z = plus (times x z) (times y z).
  Proof.
    refine (times_comm _ _ @ _).
    refine (dist_times_plus _ _ _ @ _).
    refine (ap (plus (times z x)) (times_comm _ _) @ _).
    apply (ap (fun a => plus a (times y z)) (times_comm _ _)).
  Defined.
  
  Lemma times_assoc x y : forall z, times (times x y) z = times x (times y z).
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - reflexivity.
    - intros Sz HSz.
      refine (ap (plus (times x y)) HSz @ _).
      symmetry ; apply dist_times_plus.
    - intros Pz HPz.
      refine (ap (fun z => minus z (times x y)) HPz @ _).
      unfold minus.
      refine (_ @ (dist_times_plus _ _ _)^).
      refine (ap (plus (times x (times y Pz))) _).
      apply (times_negatex _ _)^.
  Defined.

  Global Instance: Plus Z := plus.
  Global Instance: Mult Z := times.
  Global Instance: Zero Z := zero_Z.  
  Global Instance: One Z := succ zero.
  Global Instance: Negate Z := negate.
  Global Instance ring_Z : Ring Z.
  Proof.
    repeat split ; try (apply _).
    - intros x y z. symmetry. apply plus_assoc.
    - intro x. apply plus_0n.
    - intro x. apply plus_xnegate.
    - intro x. apply plus_negatex.
    - intros x y. apply plus_comm.
    - intros x y z. symmetry. apply times_assoc.
    - intros x. apply times_1n.
    - intros x y. apply times_comm.
    - intros x y z.
      apply dist_times_plus.
  Defined.

End ring_Z.

Section initial_Z.
  Variable A : Type.
  Context `{Ring A}.

  Definition ZtoA : Z -> A.
  Proof.
    hinduction ; simpl.
    - apply zero.
    - apply (Aplus one).
    - apply (Aplus (Anegate one)).
    - intros.
      symmetry.
      refine (associativity _ _ _ @ _).
      refine (ap (fun z => z & m) (left_inverse _) @ _).
      ring_with_nat.
    - intros.
      symmetry.
      refine (associativity _ _ _ @ _).
      refine (ap (fun z => z & m) (right_inverse _) @ _).
      ring_with_nat.
  Defined.

  Lemma ZtoAplus x : forall y, ZtoA (plus x y) = Aplus (ZtoA x) (ZtoA y).
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - ring_with_nat.
    - intros n X.
      refine (ap (Aplus Aone) X @ _).
      ring_with_nat.
    - intros.
      refine (ap (Aplus (Anegate Aone)) X @ _).
      ring_with_nat.
  Defined.

  Lemma ZtoAnegate : forall x, ZtoA (negate x) = Anegate (ZtoA x).
  Proof.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - symmetry.
      apply negate_0.
    - intros n X.
      refine (ap (Aplus (Anegate Aone)) X @ _).
      symmetry.
      apply negate_plus_distr.
    - intros n X.
      refine (ap (Aplus Aone) X @ _).
      refine (ap (fun z => Aplus z (Anegate (ZtoA n))) (negate_involutive Aone)^ @ _).
      symmetry.
      apply negate_plus_distr.
  Defined.  

  Instance: SemiRingPreserving ZtoA.
  Proof.
    repeat split.
    - intro x.
      hinduction ; simpl ; try (intros ; apply set_path2).
      * ring_with_nat.
      * intros y X.
        refine (ap (Aplus Aone) X @ _).
        ring_with_nat.
      * intros y X.
        refine (ap (Aplus (Anegate Aone)) X @ _).
        ring_with_nat.
    - intro x.
      hinduction ; simpl ; try (intros ; apply set_path2).
      * ring_with_nat.
      * intros y X ; cbn.
        refine (ZtoAplus x _ @ _).
        refine (ap (Aplus (ZtoA x)) X @ _).
        ring_with_nat.
      * intros y X.
        cbn.
        refine (ZtoAplus _ _ @ _).
        refine (ap (Aplus _) (ZtoAnegate _) @ _).
        refine (ap (fun z => Aplus z _) X @ _).
        refine (_ @ ap (fun z => ZtoA x & z) (commutativity (ZtoA y) (Anegate Aone))).
        refine (_ @ (distribute_l (ZtoA x) _ _)^).
        refine (ap (Aplus (ZtoA x & ZtoA y)) _).
        refine (_ @ commutativity _ (ZtoA x)).
        apply negate_mult.
    - unfold UnitPreserving ; compute.
      apply H.
  Defined.
  
  Theorem uniqueness (f : Z -> A) {H0 : SemiRingPreserving f} : forall x, ZtoA x = f x.
  Proof.
    assert (f (succ zero_Z) = Aone) as fone.
    { apply H0. }
    assert (forall x y, f(plus x y) = Aplus (f x) (f y)) as fplus.
    { apply H0. }
    compute-[times plus ZtoA] in *.
    hinduction ; simpl ; try (intros ; apply set_path2).
    - symmetry. apply H0.
    - intros x Hx.
      refine (ap (Aplus _) Hx @ _).
      refine (ap (fun z => Aplus z (f x)) fone^ @ _).
      refine ((fplus _ _)^ @ _).
      refine (ap f _).
      refine (plus_Sn _ _ @ _).
      refine (ap succ (plus_0n _)).
    - intros x Hx.
      refine (ap (Aplus _) Hx @ _).
      refine (ap (fun z => Aplus (Anegate z) (f x)) fone^ @ _).
      refine (ap (fun z => Aplus z (f x)) _ @ _).
      * symmetry. apply preserves_negate.
      * refine ((fplus _ _)^ @ _).
        refine (ap f _) ; cbn.
        refine (plus_Pn _ _ @ _).
        apply (ap pred (plus_0n x)).
  Defined.

End initial_Z.
        
        
        
        
      
    
      
      
      
      
    
    
Module Export AltInts.

  Private Inductive Z' : Type0 :=
  | positive : nat -> Z'
  | negative : nat -> Z'.

  Axiom path : positive 0 = negative 0.

  Section AltIntsInd.
    Variable (P : Z' -> Type)
             (po : forall (x : nat), P (positive x))
             (ne : forall (x : nat), P (negative x))
             (i : path # (po 0) = ne 0).            

    Fixpoint Z'_ind (x : Z') {struct x} : P x
      := 
        (match x return _ -> P x with
         | positive n => fun _ => po n
         | negative n => fun _ => ne n
         end) i.

    Axiom Z'_ind_beta_path : apD Z'_ind path = i.
  End AltIntsInd.

  Section AltIntsRec.
    Variable (P : Type)
             (po : nat -> P)
             (pn : nat -> P)
             (i : po 0 = pn 0).

    Definition Z'_rec : Z' -> P.
    Proof.
      simple refine (Z'_ind _ _ _ _) ; simpl.
      - apply po.
      - apply pn.
      - refine (transport_const _ _ @ i).
    Defined.

    Definition Z'_rec_beta_path : ap Z'_rec path = i.
    Proof.
      unfold Z_rec.
      eapply (cancelL (transport_const path _)).
      simple refine ((apD_const _ _)^ @ _).
      apply Z'_ind_beta_path.
    Defined.
    
  End AltIntsRec.

  Instance Z'_recursion : HitRecursion Z' :=
    {
      indTy := _; recTy := _; 
      H_inductor := Z'_ind; H_recursor := Z'_rec
    }.
    
End AltInts.

Section Isomorphic.

  Definition succ_Z' : Z' -> Z'.
  Proof.
    simple refine (Z'_rec _ _ _ _).
    - apply (fun n => positive (S n)).
    - induction 1 as [ | n].
      * apply (positive 1).
      * apply (negative n).
    - reflexivity.
  Defined.

  Definition pred_Z' : Z' -> Z'.
  Proof.
    simple refine (Z'_rec _ _ _ _).
    - induction 1 as [ | n].
      * apply (negative 1).
      * apply (positive n).
    - intro n.
      apply (negative (S n)).
    - reflexivity.
  Defined.

  Fixpoint Nat_to_Pos (n : nat) : Int.Pos :=
    match n with
    | 0 => Int.one
    | S k => succ_pos (Nat_to_Pos k)
    end.

  Definition Z'_to_Int : Z' -> Int.
  Proof.
    simple refine (Z'_rec _ _ _ _).
    - induction 1 as [ | n IHn].
      apply (Int.zero).
      apply (succ_int IHn).
    - induction 1 as [ | n IHn].
      apply (Int.zero).
      apply (pred_int IHn).
    - reflexivity.
  Defined.

  Definition Pos_to_Nat : Int.Pos -> nat.
  Proof.
    induction 1 as [ | n IHn].
    - apply 1.
    - apply (S IHn).
  Defined.

  Definition Int_to_Z' (x : Int) : Z'.
  Proof.
    induction x as [p | | p].
    apply (negative (Pos_to_Nat p)).
    apply (positive 0).
    apply (positive (Pos_to_Nat p)).
  Defined.

  Definition Z'_to_int_pos_homomorphism n : 
    Z'_to_Int (positive (S n)) = succ_int (Z'_to_Int (positive n)) := idpath.

  Definition Z'_to_int_neg_homomorphism n : 
    Z'_to_Int (negative (S n)) = pred_int (Z'_to_Int (negative n)) := idpath.

  Theorem Int_to_Z'_to_Int : forall x : Int, Z'_to_Int(Int_to_Z' x) = x.
  Proof.
    induction x as [p | | p].
    - induction p as [ | p IHp ].
      * reflexivity.
      * refine (Z'_to_int_neg_homomorphism _ @ ap pred_int IHp).
    - reflexivity.
    - induction p as [ | p IHp ].
      * reflexivity.
      * refine (Z'_to_int_pos_homomorphism _ @ ap succ_int IHp).
  Defined.

  Lemma Int_to_Z'_succ_homomorphism :
    forall x, Int_to_Z' (succ_int x) = succ_Z' (Int_to_Z' x).
  Proof.
    induction x as [p | | p].
    - induction p as [ | p IHp] ; cbn.
      * apply path.
      * reflexivity.
    - reflexivity.
    - induction p ; reflexivity.
  Defined.
  
  Lemma Int_to_Z'_pred_homomorphism :
    forall x : Int, Int_to_Z' (pred_int x) = pred_Z' (Int_to_Z' x).
  Proof.
    induction x as [p | | p] ; try (induction p) ; reflexivity.
  Defined.
  
  Theorem Z'_to_Int_to_Z' : forall x : Z', Int_to_Z'(Z'_to_Int x) = x.
  Proof.
    simple refine (Z'_ind _ _ _ _) ; simpl.
    - induction x as [ | x] ; simpl.
      * reflexivity.
      * refine (ap Int_to_Z' (Z'_to_int_pos_homomorphism _)^ @ _) ; simpl.
        refine (Int_to_Z'_succ_homomorphism _ @ _).
        apply (ap succ_Z' IHx).
    - induction x as [ | x IHx] ; simpl.
      * apply path.
      * refine (ap Int_to_Z' (Z'_to_int_neg_homomorphism _)^ @ _) ; simpl.
        refine (Int_to_Z'_pred_homomorphism _ @ _).
        apply (ap pred_Z' IHx).
    - simpl.
      refine (transport_paths_FlFr path _ @ _).
      refine (ap (fun z => _ @ z) (ap_idmap _) @ _).
      refine (ap (fun z => z @ _) (concat_p1 _) @ _).
      assert (ap (fun x : Z' => Z'_to_Int x) path = idpath) as X.
      {
        apply axiomK_hset ; apply hset_int.
      }
      refine (ap (fun z => z^ @ path) (ap_compose Z'_to_Int Int_to_Z' path) @ _).
      refine (ap (fun z => (ap Int_to_Z' z)^ @ _) X @ _).
      apply concat_1p.      
  Defined.

  Definition biinv_Int_to_Z' : BiInv Int_to_Z' :=
    ((Z'_to_Int ; Int_to_Z'_to_Int), (Z'_to_Int ; Z'_to_Int_to_Z')).

  Instance equiv_Int_to_Z' : IsEquiv Int_to_Z' :=
    isequiv_biinv _ biinv_Int_to_Z'.

  Instance Z'_set : IsHSet Z'.
  Proof.
    apply (trunc_equiv Int Int_to_Z').
  Defined.

  Definition Z_to_Z' : Z -> Z'.
  Proof.
    hrecursion.
    - apply (positive 0).
    - apply succ_Z'.
    - apply pred_Z'.
    - hinduction.
      * apply (fun _ => idpath).
      * induction x as [ | x IHx] ; simpl.
        ** apply path^.
        ** reflexivity.
      * apply set_path2.
    - hinduction.
      * induction x as [ | x IHx] ; simpl.
        ** apply path.
        ** reflexivity.
      * apply (fun _ => idpath).
      * apply set_path2.
  Defined.
  
  Definition Z'_to_Z : Z' -> Z.
  Proof.
    hrecursion.
    - induction 1 as [ | x IHx].
      * apply zero_Z.
      * apply (succ IHx).
    - induction 1 as [ | x IHx].
      * apply zero_Z.
      * apply (pred IHx).
    - reflexivity.
  Defined.

  Theorem Z'_to_Z_to_Z' : forall n : Z', Z_to_Z'(Z'_to_Z n) = n.
  Proof.
    hinduction.
    - induction x as [ | x IHx] ; cbn.
      * reflexivity.
      * apply (ap succ_Z' IHx).
    - induction x as [ | x IHx] ; cbn.
      * apply path.
      * apply (ap pred_Z' IHx).
    - apply set_path2.
  Defined.

  Lemma Z'_to_Z_succ : forall n, Z'_to_Z(succ_Z' n) = succ(Z'_to_Z n).
  Proof.
    hinduction.
    - apply (fun _ => idpath).
    - induction x.
      * reflexivity.
      * apply inv2.
    - apply set_path2.
  Defined.

  Lemma Z'_to_Z_pred : forall n, Z'_to_Z(pred_Z' n) = pred(Z'_to_Z n).
  Proof.
    hinduction.
    - induction x.
      * reflexivity.
      * apply inv1.
    - apply (fun _ => idpath).
    - apply set_path2.
  Defined. 

  Theorem Z_to_Z'_to_Z : forall n : Z, Z'_to_Z(Z_to_Z' n) = n.
  Proof.
    hinduction ; try (intros ; apply set_path2).
    - reflexivity.
    - intros x Hx.
      refine (_ @ ap succ Hx).
      apply Z'_to_Z_succ.
    - intros x Hx.
      refine (_ @ ap pred Hx).
      apply Z'_to_Z_pred.
  Defined.

  Definition biinv_Z'_to_Z : BiInv Z'_to_Z :=
    ((Z_to_Z' ; Z'_to_Z_to_Z'), (Z_to_Z' ; Z_to_Z'_to_Z)).

  Definition equiv_Z'_to_Z : IsEquiv Z'_to_Z :=
    isequiv_biinv _ biinv_Z'_to_Z.

End Isomorphic.
