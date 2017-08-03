Require Import HoTT.
Require Import disjunction lattice.

Section subobjects.
  Variable A : Type.

  Definition Sub := A -> hProp.

  Definition empty_sub : Sub := fun _ => False_hp.

  Definition singleton (a : A) : Sub := fun b => BuildhProp (Trunc (-1) (b = a)).
End subobjects.

Arguments empty_sub {_}.
Arguments singleton {_} _.

Section sub_classes.
  Context {A : Type}.
  Variable C : (A -> hProp) -> hProp.
  Context `{Univalence}.

  Instance blah : Lattice (Sub A).
  Proof.
    unfold Sub.
    apply _.
  Defined.  

  Definition hasUnion := forall X Y, C X -> C Y -> C (max_fun X Y).
  Definition hasIntersection := forall X Y, C X -> C Y -> C (min_fun X Y).
  Definition hasEmpty := C empty_sub.
  Definition hasSingleton := forall a, C (singleton a).
  Definition hasDecidableEmpty := forall X, C X -> hor (X = empty_sub) (hexists (fun a => X a)).
End sub_classes.

Section isIn.
  Variable A : Type.
  Variable C : (A -> hProp) -> hProp.

  Context `{Univalence}.
  Context {HS : hasSingleton C} {HIn : forall X, C X -> forall a, Decidable (X a)}.

  Theorem decidable_A_isIn : forall a b : A, Decidable (Trunc (-1) (b = a)).
  Proof.
    intros.
    unfold Decidable, hasSingleton in *.
    pose (HIn (singleton a) (HS a) b).
    destruct s.
    - unfold singleton in t.
      left.
      apply t.
    - right.
      intro p.
      unfold singleton in n.
      strip_truncations.
      contradiction (n (tr p)).
  Defined.

End isIn.

Context `{Univalence}.

Instance koe : forall (T : Type) (Ttrunc : IsHProp T), IsTrunc (-1) (T + ~T).
Proof.
  intros.
  apply (equiv_hprop_allpath _)^-1.
  intros [x | nx] [y | ny] ; try f_ap ; try (apply Ttrunc) ; try contradiction.
  - apply equiv_hprop_allpath. apply _.
Defined.    

Section intersect.
  Variable A : Type.
  Variable C : (Sub A) -> hProp.

  Context `{Univalence}.
  Context
    {HI :hasIntersection C} {HE : hasEmpty C}
    {HS : hasSingleton C} {HDE : hasDecidableEmpty C}.

  Theorem decidable_A_intersect : forall a b : A, Decidable (Trunc (-1) (b = a)).
  Proof.
    intros.
    unfold Decidable, hasEmpty, hasIntersection, hasSingleton, hasDecidableEmpty in *.
    pose (HI (singleton a) (singleton b) (HS a) (HS b)) as IntAB.
    pose (HDE (min_fun (singleton a) (singleton b)) IntAB) as IntE.
    Print Trunc_rec.
    refine (@Trunc_rec _ _ _  _ _ IntE) ; intros [p | p] ; unfold min_fun, singleton in p.
    - right.
      pose (apD10 p b) as pb ; unfold empty_sub in pb ; cbn in pb.
      assert (BuildhProp (Trunc (-1) (b = b)) = Unit_hp).
      {
        apply path_iff_hprop.
        - apply (fun _ => tt).
        - apply (fun _ => tr idpath).          
      }
      rewrite X in pb.
      unfold Unit_hp in pb.
      assert (forall P : hProp, land P Unit_hp = P).
      {
        intro P.
        apply path_iff_hprop.
        - intros [x _] ; assumption.
        - apply (fun x => (x, tt)).          
      }
      rewrite (X0 (BuildhProp (Trunc (-1) (b = a)))) in pb.
      intro q.
      assert (BuildhProp (Trunc (-1) (b = a))).
      {
        apply q.
      }
      apply (pb # X1).
    - strip_truncations.
      destruct p as [a0 [t1 t2]].
      strip_truncations.
      apply (inl (tr (t2^ @ t1))).
  Defined.
End intersect.