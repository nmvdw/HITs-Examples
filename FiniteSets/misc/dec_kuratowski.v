(** We show that some operations on [FSet A] only exists when [A] has decidable equality. *)
Require Import HoTT.
Require Import FSets.

Section membership.
  Context {A : Type} `{Univalence}.

  Theorem dec_membership
          (H1 : forall (a : A) (X : FSet A), Decidable(a ∈ X))
          (a b : A)
    : Decidable(merely(a = b)).
  Proof.
    destruct (H1 a {|b|}) as [t | t].
    - apply (inl t).
    - apply (inr(fun p => t p)).
  Defined.
End membership.

Section intersection.
  Context {A : Type} `{Univalence}.

  Variable (int : FSet A -> FSet A -> FSet A)
           (int_member : forall (a : A) (X Y : FSet A),
               a ∈ (int X Y) = BuildhProp(a ∈ X * a ∈ Y)).

  Theorem dec_intersection (a b : A) : Decidable(merely(a = b)).
  Proof.
    destruct (merely_choice (int {|a|} {|b|})) as [p | p].
    - refine (inr(fun X => _)).
      strip_truncations.
      refine (transport (fun z => a ∈ z) p _).
      rewrite (int_member a {|a|} {|b|}), X.
      split ; apply (tr idpath).
    - left.
      strip_truncations.
      destruct p as [c p].
      rewrite int_member in p.
      destruct p as [p1 p2].
      strip_truncations.
      apply (tr(p1^ @ p2)).
  Defined.  
End intersection.

Section subset.
  Context {A : Type} `{Univalence}.

  Theorem dec_subset
          (H1 : forall (X Y : FSet A), Decidable(X ⊆ Y))
          (a b : A)
    : Decidable(merely(a = b)).
  Proof.
    destruct (dec ({|a|} ⊆ {|b|})) as [t | t].
    - apply (inl t).
    - apply (inr(fun p => t p)).
  Defined.
End subset.  
      
Section decidable_equality.
  Context {A : Type} `{Univalence}.

  Theorem dec_decidable_equality : DecidablePaths(FSet A)
                                   -> forall (a b : A), Decidable(merely(a = b)).
  Proof.
    intros H1 a b.
    specialize (H1 {|a|} {|b|}).
    destruct H1 as [p | p].
    - pose (transport (fun z => a ∈ z) p) as t.
      apply (inl (t (tr idpath))).
    - refine (inr (fun n => _)).
      strip_truncations.
      pose (transport (fun z => {|a|} = {|z|}) n) as t.
      apply (p (t idpath)).
  Defined.
End decidable_equality.

Section length.
  Context {A : Type} `{Univalence}.

  Variable (length : FSet A -> nat)
           (length_singleton : forall (a : A), length {|a|} = 1)
           (length_one : forall (X : FSet A), length X = 1 -> {a : A & X = {|a|}}).

  Theorem dec_length (a b : A) : Decidable(merely(a = b)).
  Proof.
    destruct (dec (length ({|a|} ∪ {|b|}) = 1)).
    - destruct (length_one _ p) as [c Xc].
      refine (inl _).
      assert (merely(a = c) * merely(b = c)).
      { split.
        * pose (transport (fun z => a ∈ z) Xc) as t.
          apply (t(tr(inl(tr idpath)))).
        * pose (transport (fun z => b ∈ z) Xc) as t.
          apply (t(tr(inr(tr idpath)))).
      }
      destruct X as [X1 X2] ; strip_truncations.
      apply (tr (X1 @ X2^)).
    - refine (inr(fun p => _)).
      strip_truncations.
      rewrite p, idem in n.
      apply (n (length_singleton b)).
  Defined.
End length.