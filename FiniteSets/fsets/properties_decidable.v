(* Properties of [FSet A] where [A] has decidable equality *)
Require Import HoTT HitTactics.
From fsets Require Export properties extensionality operations_decidable.
Require Export lattice.

(* Lemmas relating operations to the membership predicate *)
Section operations_isIn.

  Context {A : Type} `{DecidablePaths A} `{Univalence}.

  Lemma ext : forall (S T : FSet A), (forall a, isIn_b a S = isIn_b a T) -> S = T.
  Proof.
    intros X Y H2.
    apply fset_ext.
    intro a.
    specialize (H2 a).
    unfold isIn_b, dec in H2.
    destruct (isIn_decidable a X) ; destruct (isIn_decidable a Y).
    - apply path_iff_hprop ; intro ; assumption.
    - contradiction (true_ne_false).
    - contradiction (true_ne_false) ; apply H2^.
    - apply path_iff_hprop ; intro ; contradiction.
  Defined.

  Lemma empty_isIn (a : A) :
    isIn_b a ∅ = false.
  Proof.
    reflexivity.
  Defined.

  Lemma L_isIn (a b : A) :
    isIn a {|b|} -> a = b.
  Proof.
    intros. strip_truncations. assumption.
  Defined.

  Lemma L_isIn_b_true (a b : A) (p : a = b) :
    isIn_b a {|b|} = true.
  Proof.
    unfold isIn_b, dec.
    destruct (isIn_decidable a {|b|}) as [n | n] .
    - reflexivity.
    - simpl in n.
      contradiction (n (tr p)).
  Defined.

  Lemma L_isIn_b_aa (a : A) :
    isIn_b a {|a|} = true.
  Proof.
    apply L_isIn_b_true ; reflexivity.
  Defined.

  Lemma L_isIn_b_false (a b : A) (p : a <> b) :
    isIn_b a {|b|} = false.
  Proof.
    unfold isIn_b, dec.
    destruct (isIn_decidable a {|b|}).
    - simpl in t.
      strip_truncations.
      contradiction.
    - reflexivity.
  Defined.
  
  (* Union and membership *)
  Lemma union_isIn (X Y : FSet A) (a : A) :
    isIn_b a (U X Y) = orb (isIn_b a X) (isIn_b a Y).
  Proof.
    unfold isIn_b ; unfold dec.
    simpl.
    destruct (isIn_decidable a X) ; destruct (isIn_decidable a Y) ; reflexivity.
  Defined.

  Lemma intersection_isIn (X Y: FSet A) (a : A) :
    isIn_b a (intersection X Y) = andb (isIn_b a X) (isIn_b a Y).
  Proof.
    hinduction X; try (intros ; apply set_path2).
    - reflexivity.
    - intro b.
      destruct (dec (a = b)).
      * rewrite p.
        destruct (isIn_b b Y) ; symmetry ; eauto with bool_lattice_hints.
      * destruct (isIn_b b Y) ; destruct (isIn_b a Y) ; symmetry ; eauto with bool_lattice_hints.
      + rewrite and_false.
        symmetry.
        apply (L_isIn_b_false a b n).
      + rewrite and_true.
        apply (L_isIn_b_false a b n).
    - intros X1 X2 P Q.
      rewrite union_isIn ; rewrite union_isIn.
      rewrite P.
      rewrite Q.
      unfold isIn_b, dec.
      destruct (isIn_decidable a X1)
      ; destruct (isIn_decidable a X2)
      ; destruct (isIn_decidable a Y)
      ; reflexivity.
  Defined.

  Lemma comprehension_isIn (Y : FSet A) (ϕ : A -> Bool) (a : A) :
    isIn_b a (comprehension ϕ Y) = andb (isIn_b a Y) (ϕ a).
  Proof.
    hinduction Y ; try (intros; apply set_path2). 
    - apply empty_isIn.
    - intro b.
      destruct (isIn_decidable a {|b|}).
      * simpl in t.
        strip_truncations.
        rewrite t.
        destruct (ϕ b).
        ** rewrite (L_isIn_b_true _ _ idpath).
           eauto with bool_lattice_hints.
        ** rewrite empty_isIn ; rewrite (L_isIn_b_true _ _ idpath).
           eauto with bool_lattice_hints.
      * destruct (ϕ b).
        ** rewrite L_isIn_b_false.
           *** eauto with bool_lattice_hints.
           *** intro. 
               apply (n (tr X)).
        ** rewrite empty_isIn.
           rewrite L_isIn_b_false.
           *** eauto with bool_lattice_hints.
           *** intro.
               apply (n (tr X)).
    - intros.
      Opaque isIn_b.
      rewrite ?union_isIn.
      rewrite X.
      rewrite X0.
      assert (forall b1 b2 b3,
                 (b1 && b2 || b3 && b2)%Bool = ((b1 || b3) && b2)%Bool).
      { intros ; destruct b1, b2, b3 ; reflexivity. }
      apply X1.
  Defined.
End operations_isIn.

(* Some suporting tactics *)
(*
Ltac simplify_isIn :=
  repeat (rewrite union_isIn
          || rewrite L_isIn_b_aa      
          || rewrite intersection_isIn
          || rewrite comprehension_isIn).
 *)

Ltac simplify_isIn :=
  repeat (rewrite union_isIn
       || rewrite L_isIn_b_aa      
       || rewrite intersection_isIn
       || rewrite comprehension_isIn).

Ltac toBool := try (intro) ;
               intros ; apply ext ; intros ; simplify_isIn ; eauto with bool_lattice_hints typeclass_instances.

Section SetLattice.

  Context {A : Type}.
  Context {A_deceq : DecidablePaths A}.
  Context `{Univalence}.

  Instance fset_max : maximum (FSet A) := U.
  Instance fset_min : minimum (FSet A) := intersection.
  Instance fset_bot : bottom (FSet A) := E.

  Instance lattice_fset : Lattice (FSet A).
  Proof.
    split ; toBool.      
  Defined.
  
<<<<<<< HEAD
=======
  Instance lattice_fset : Lattice intersection (@U A)  (@E A) :=
    {
      commutative_min := _ ;
      commutative_max := _ ;
      associative_min := _ ;
      associative_max := _ ;
      idempotent_min := _ ;
      idempotent_max := _ ;
      neutralL_max := _ ;
      neutralR_max := _ ;
      absorption_min_max := _ ;
      absorption_max_min := _
    }.

>>>>>>> 8a65852d1b39137898bddbaf7cf949bceeb4a574
End SetLattice.

(* Comprehension properties *)
Section comprehension_properties.

  Opaque isIn_b.

  Context {A : Type}.
  Context {A_deceq : DecidablePaths A}.
  Context `{Univalence}.

  Lemma comprehension_or : forall ϕ ψ (x: FSet A),
      comprehension (fun a => orb (ϕ a) (ψ a)) x
      = U (comprehension ϕ x) (comprehension ψ x).
  Proof.
    toBool.
  Defined.
  
  (** comprehension properties *)
  Lemma comprehension_false Y : comprehension (fun (_ : A) => false) Y = E.
  Proof.
    toBool.
  Qed.

  Lemma comprehension_all : forall (X : FSet A),
      comprehension (fun a => isIn_b a X) X = X.
  Proof.
    toBool.
  Qed.
  
  Lemma comprehension_subset : forall ϕ (X : FSet A),
      U (comprehension ϕ X) X = X.
  Proof.
    toBool.
  Defined.
  
End comprehension_properties.

(* With extensionality we can prove decidable equality *)
Section dec_eq.
  Context (A : Type) `{DecidablePaths A} `{Univalence}.

  Instance decidable_prod {X Y : Type} `{Decidable X} `{Decidable Y} :
    Decidable (X * Y).
  Proof.
    unfold Decidable in *.
    destruct H1 as [x | nx] ; destruct H2 as [y | ny].
    - left ; split ; assumption.
    - right. intros [p1 p2]. contradiction.
    - right. intros [p1 p2]. contradiction.
    - right. intros [p1 p2]. contradiction.
  Defined.
  
  Instance fsets_dec_eq : DecidablePaths (FSet A).
  Proof.
    intros X Y.
    apply (decidable_equiv' ((subset Y X) * (subset X Y)) (eq_subset X Y)^-1).
    apply _.
  Defined.

End dec_eq.
