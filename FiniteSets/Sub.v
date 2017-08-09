Require Import HoTT.
Require Import disjunction lattice notation.

Section subobjects.
  Variable A : Type.

  Definition Sub := A -> hProp.

  Global Instance sub_empty : hasEmpty Sub := fun _ => False_hp.
  Global Instance sub_union : hasUnion Sub := max_fun.
  Global Instance sub_intersection : hasIntersection Sub := min_fun.
  Global Instance sub_singleton : hasSingleton Sub A
    := fun a b => BuildhProp (Trunc (-1) (b = a)).
  Global Instance sub_membership : hasMembership Sub A := fun a X => X a.
  Global Instance sub_comprehension : hasComprehension Sub A
    := fun ϕ X a => BuildhProp (X a * (ϕ a = true)).
  Global Instance sub_subset `{Univalence} : hasSubset Sub
    := fun X Y => BuildhProp (forall a, X a -> Y a).

End subobjects.

Section sub_classes.
  Context {A : Type}.
  Variable C : (A -> hProp) -> hProp.
  Context `{Univalence}.

  Instance subobject_lattice : Lattice (Sub A).
  Proof.
    apply _.
  Defined.  

  Definition closedUnion := forall X Y, C X -> C Y -> C (X ∪ Y).
  Definition closedIntersection := forall X Y, C X -> C Y -> C (X ∩ Y).
  Definition closedEmpty := C ∅.
  Definition closedSingleton := forall a, C {|a|}.
  Definition hasDecidableEmpty := forall X, C X -> hor (X = ∅) (hexists (fun a => a ∈ X)).
End sub_classes.

Section isIn.
  Variable A : Type.
  Variable C : (A -> hProp) -> hProp.

  Context `{Univalence}.
  Context {HS : closedSingleton C} {HIn : forall X, C X -> forall a, Decidable (X a)}.

  Theorem decidable_A_isIn : forall a b : A, Decidable (Trunc (-1) (b = a)).
  Proof.
    intros.
    unfold Decidable, closedSingleton in *.
    pose (HIn {|a|} (HS a) b).
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

Section intersect.
  Variable A : Type.
  Variable C : (Sub A) -> hProp.
  Context `{Univalence}.

  Global Instance hprop_lem : forall (T : Type) (Ttrunc : IsHProp T), IsHProp (T + ~T).
  Proof.
    intros.
    apply (equiv_hprop_allpath _)^-1.
    intros [x | nx] [y | ny] ; try f_ap ; try (apply Ttrunc) ; try contradiction.
    - apply equiv_hprop_allpath. apply _.
  Defined.

  Context
    {HI : closedIntersection C} {HE : closedEmpty C}
    {HS : closedSingleton C} {HDE : hasDecidableEmpty C}.

  Theorem decidable_A_intersect : forall a b : A, Decidable (Trunc (-1) (b = a)).
  Proof.
    intros.
    unfold Decidable, closedEmpty, closedIntersection, closedSingleton, hasDecidableEmpty in *.
    pose (HI {|a|} {|b|} (HS a) (HS b)) as IntAB.
    pose (HDE ({|a|} ∪ {|b|}) IntAB) as IntE.
    refine (@Trunc_rec _ _ _  _ _ IntE) ; intros [p | p] ; unfold min_fun, singleton in p.
    - right.
      intro q.
      strip_truncations.
      rewrite q in p.
      enough (a ∈ ∅) as X.
      { apply X. }
      rewrite <- p.
      cbn.
      split ; apply (tr idpath).
    - strip_truncations.
      destruct p as [a0 [t1 t2]].
      strip_truncations.
      apply (inl (tr (t2^ @ t1))).
  Defined.
End intersect.

Section finite_hott.
  Variable A : Type.
  Context `{Univalence} `{IsHSet A}.
  
  Definition finite (X : Sub A) : hProp := BuildhProp (Finite {a : A & a ∈ X}).

  Definition singleton : closedSingleton finite.
  Proof.
    intros a.
    simple refine (Build_Finite _ _ _).
    - apply 1.
    - apply tr.
      simple refine (BuildEquiv _ _ _ _).
      * apply (fun _ => inr tt).
      * simple refine (BuildIsEquiv _ _ _ _ _ _ _) ; unfold Sect in *.
        ** apply (fun _ => (a;tr idpath)).
        ** intros x ; destruct x as [ | x] ; try contradiction.
           destruct x ; reflexivity.
        ** intros [b bp] ; simpl.
           strip_truncations.
           simple refine (path_sigma _ _ _ _ _).
           *** apply bp^.
           *** apply path_ishprop.
        ** intros.
           apply path_ishprop.
  Defined.

  Definition empty_finite : closedEmpty finite.
  Proof.
    simple refine (Build_Finite _ _ _).
    - apply 0.
    - apply tr.
      simple refine (BuildEquiv _ _ _ _).
      intros [a p] ; apply p.
  Defined.

  Definition decidable_empty_finite : hasDecidableEmpty finite.
  Proof.
    intros X Y.
    destruct Y as [n Xn].
    strip_truncations.
    simpl in Xn.
    destruct Xn as [f [g fg gf adj]].
    destruct n.
    - refine (tr(inl _)).
      unfold empty.
      apply path_forall.
      intro z.
      apply path_iff_hprop.
      * intros p.
        contradiction (f(z;p)).
      * contradiction.
    - refine (tr(inr _)).
      apply (tr(g(inr tt))).
  Defined.
  
  Lemma no_union
        (f : forall (X Y : Sub A),
            Finite {a : A & X a} -> Finite {a : A & Y a}
            -> Finite ({a : A & (X ∪ Y) a}))
        (a b : A)
    :
      hor (a = b) (a = b -> Empty).
  Proof.
    specialize (f {|a|} {|b|} (singleton a) (singleton b)).
    destruct f as [n pn].
    strip_truncations.
    destruct pn as [f [g fg gf adj]].
    unfold Sect in *.
    destruct n.
    - cbn in *. contradiction f.
      exists a.
      apply (tr(inl(tr idpath))).
    - destruct n ; cbn in *.
      -- pose ((a;tr(inl(tr idpath)))
               : {a0 : A & Trunc (-1) (Trunc (-1) (a0 = a) + Trunc (-1) (a0 = b))})
         as s1.
         pose ((b;tr(inr(tr idpath)))
               : {a0 : A & Trunc (-1) (Trunc (-1) (a0 = a) + Trunc (-1) (a0 = b))})
         as s2.
         pose (f s1) as fs1.
         pose (f s2) as fs2.
         assert (fs1 = fs2) as fs_eq.
         { apply path_ishprop. }
         pose (g fs1) as gfs1.
         pose (g fs2) as gfs2.
         refine (tr(inl _)).
         refine (ap (fun x => x.1) (gf s1)^ @ _ @ (ap (fun x => x.1) (gf s2))). 
         unfold fs1, fs2 in fs_eq. rewrite fs_eq.
         reflexivity.
      -- refine (tr(inr _)).
         intros p.
         pose (inl(inr tt) : Fin n + Unit + Unit) as s1.
         pose (inr tt : Fin n + Unit + Unit) as s2.
         pose (g s1) as gs1.
         pose (c := g s1).
         assert (c = gs1) as ps1. reflexivity.
         pose (g s2) as gs2.
         pose (d := g s2).
         assert (d = gs2) as ps2. reflexivity.
         pose (f gs1) as gfs1.
         pose (f gs2) as gfs2.
         destruct c as [x px] ; destruct d as [y py].
         simple refine (Trunc_ind _ _ px) ; intros p1.
         simple refine (Trunc_ind _ _ py) ; intros p2.
         simpl.
         assert (x = y -> Empty) as X1.
         {
           enough (s1 = s2) as X.
           {
             intros. 
             unfold s1, s2 in X.
             refine (not_is_inl_and_inr' (inl(inr tt)) _ _).
             + apply tt.
             + rewrite X ; apply tt.
           }
           transitivity gfs1.
           { unfold gfs1, s1. apply (fg s1)^. }
           symmetry ; transitivity gfs2.
           { unfold gfs2, s2. apply (fg s2)^. }
           unfold gfs2, gfs1.
           rewrite <- ps1, <- ps2.
           f_ap.
           simple refine (path_sigma _ _ _ _ _).
           * cbn.
             destruct p1 as [p1 | p1] ; destruct p2 as [p2 | p2] ; strip_truncations.
             ** apply (p2 @ p1^).
             ** refine (p2 @ _^ @ p1^). auto.
             ** refine (p2 @ _ @ p1^). auto.
             ** apply (p2 @ p1^).                              
           * apply path_ishprop.
         }
         apply X1.
         destruct p1 as [p1 | p1] ; destruct p2 as [p2 | p2] ; strip_truncations.
         ** apply (p1 @ p2^).
         ** refine (p1 @ _ @ p2^). auto.
         ** refine (p1 @ _ @ p2^). symmetry. auto.
         ** apply (p1 @ p2^).
  Defined.
End finite_hott.