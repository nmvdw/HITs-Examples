Require Import HoTT HitTactics.
Require Import variations.k_finite variations.b_finite.
Require Import FSets.
Require Import representations.T.

Class IsProjective (X : Type) :=
  projective : forall {P Q : Type} (p : P -> Q) (f : X -> Q),
      IsSurjection p -> hexists (fun (g : X -> P) => p o g = f).

Instance IsProjective_IsHProp `{Univalence} X : IsHProp (IsProjective X).
Proof. unfold IsProjective. apply _. Defined.

Instance Unit_Projective `{Univalence} : IsProjective Unit.
Proof.
  intros P Q p f Hsurj.
  pose (x' := center (merely (hfiber p (f tt)))).
  simple refine (@Trunc_rec (-1) (hfiber p (f tt)) _ _ _ x'). clear x'; intro x.
  simple refine (tr (fun _ => x.1;_)). simpl.
  apply path_forall; intros [].
  apply x.2.
Defined.

Instance Empty_Projective `{Univalence} : IsProjective Empty.
Proof.
  intros P Q p f Hsurj.
  apply tr. exists Empty_rec.
  apply path_forall. intros [].
Defined.

Instance Sum_Projective `{Univalence} {A B: Type} `{IsProjective A} `{IsProjective B} :
  IsProjective (A + B).
Proof.
  intros P Q p f Hsurj.
  pose (f1 := fun a => f (inl a)).
  pose (f2 := fun b => f (inr b)).
  pose (g1' := projective p f1 Hsurj).
  pose (g2' := projective p f2 Hsurj).
  simple refine (Trunc_rec _ g1') ; intros [g1 pg1].
  simple refine (Trunc_rec _ g2') ; intros [g2 pg2].
  simple refine (tr (_;_)).
  - intros [a | b].
    + apply (g1 a).
    + apply (g2 b).
  - apply path_forall; intros [a | b]; simpl.
    + apply (ap (fun h => h a) pg1).
    + apply (ap (fun h => h b) pg2).
Defined.

(* All Bishop-finite sets are projective *)
Section b_fin_projective.
  Context `{Univalence}.

  Global Instance bishop_projective (X : Type) (Hfin : Finite X) : IsProjective X.
  Proof.
    simple refine (finite_ind_hprop (fun X _ => IsProjective X) _ _ X);
      simpl; apply _.
  Defined.
End b_fin_projective.

Section k_fin_lemoo_projective.
  Context `{Univalence}.
  Context {LEMoo : forall (P : Type), Decidable P}.
  Global Instance kuratowski_projective_oo (X : Type) (Hfin : Kf X) : IsProjective X.
  Proof.
    assert (Finite X).
    { apply Kf_to_Bf; auto.
      intros pp qq. apply LEMoo. }
    apply _.
  Defined.
End k_fin_lemoo_projective.

Section k_fin_lem_projective.
  Context `{Univalence}.
  Context {LEM : forall (P : Type) {Hprop : IsHProp P}, Decidable P}.
  Variable (X : Type).
  Context `{IsHSet X}.

  Global Instance kuratowski_projective (Hfin : Kf X) : IsProjective X.
  Proof.
    assert (Finite X).
    { apply Kf_to_Bf; auto.
      intros pp qq. apply LEM. apply _. }
    apply _.
  Defined.
End k_fin_lem_projective.

Section k_fin_projective_lem.
  Context `{Univalence}.
  Variable (P : Type).
  Context `{Hprop : IsHProp P}.

  Definition X : Type := T P.
  Instance X_set : IsHSet X.
  Proof. apply _. Defined.

  Definition X_fin : Kf X.
  Proof.
    apply Kf_unfold.
    exists ({|b P|} ∪ {|c P|}).
    hinduction.
    - apply (tr (inl (tr idpath))).
    - apply (tr (inr (tr idpath))).
    - intros. apply path_ishprop.
  Defined.

  Definition p (a : Unit + Unit) : X :=
    match a with
    | inl _ => b P
    | inr _ => c P
    end.

  Instance p_surj : IsSurjection p.
  Proof.
    apply BuildIsSurjection.
    hinduction.
    - apply tr. exists (inl tt). reflexivity.
    - apply tr. exists (inr tt). reflexivity.
    - intros. apply path_ishprop.
  Defined.

  Lemma LEM `{IsProjective X} : P + ~P.
  Proof.
    pose (k := projective p idmap _).
    unfold hexists in k.
    simple refine (Trunc_rec _ k); clear k; intros [g Hg].
    destruct (dec (g (b P) = g (c P))) as [Hℵ | Hℵ].
    - left.
      assert (b P = c P) as Hbc.
      { pose (ap p Hℵ) as Hα.
        rewrite (ap (fun h => h (b P)) Hg) in Hα.
        rewrite (ap (fun h => h (c P)) Hg) in Hα.
        assumption. }
      apply (encode _ (b P) (c P) Hbc).
    - right. intros HP.
      apply Hℵ.
      apply (ap g (T.p HP)).
  Defined.
End k_fin_projective_lem.
