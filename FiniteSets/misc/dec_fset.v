Require Import HoTT HitTactics.
Require Export FSets lattice_examples.

Section quantifiers.
  Context {A : Type} `{Univalence}.
  Variable (P : A -> hProp).
 
  Definition all : FSet A -> hProp.
  Proof.
    hinduction.
    - apply Unit_hp.
    - apply P.
    - intros X Y.
      apply (BuildhProp (X * Y)).
    - eauto with lattice_hints typeclass_instances. 
    - eauto with lattice_hints typeclass_instances.
    - intros.
      apply path_trunctype ; apply prod_unit_l.
    - intros.
      apply path_trunctype ; apply prod_unit_r.
    - eauto with lattice_hints typeclass_instances.
  Defined.

  Lemma all_intro X : forall (HX : forall x, x ∈ X -> P x), all X.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - intros.
      apply tt.
    - intros.
      apply (HX a (tr idpath)).
    - intros X1 X2 HX1 HX2 Hmem.
      split.
      * apply HX1.
        intros a Ha.
        refine (Hmem a (tr _)).
        apply (inl Ha).
      * apply HX2.
        intros a Ha.
        refine (Hmem a (tr _)).
        apply (inr Ha).
  Defined.

  Lemma all_elim X a : all X -> (a ∈ X) -> P a.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - contradiction.
    - intros b Hmem Heq.
      strip_truncations.
      rewrite Heq.
      apply Hmem.
    - intros X1 X2 HX1 HX2 [Hall1 Hall2] Hmem.
      strip_truncations.
      destruct Hmem as [t | t].
      * apply (HX1 Hall1 t).
      * apply (HX2 Hall2 t). 
  Defined.      

  Definition exist : FSet A -> hProp.
  Proof.
    hinduction.
    - apply False_hp.
    - apply P.
    - apply lor.
    - eauto with lattice_hints typeclass_instances. 
    - eauto with lattice_hints typeclass_instances.
    - eauto with lattice_hints typeclass_instances.
    - eauto with lattice_hints typeclass_instances. 
    - eauto with lattice_hints typeclass_instances.
  Defined.

  Lemma exist_intro X a : a ∈ X -> P a -> exist X.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - contradiction.
    - intros b Hin Pb.
      strip_truncations.
      rewrite <- Hin.
      apply Pb.
    - intros X1 X2 HX1 HX2 Hin Pa.
      strip_truncations.
      apply tr.
      destruct Hin as [t | t].
      * apply (inl (HX1 t Pa)).
      * apply (inr (HX2 t Pa)).
  Defined.

  Lemma exist_elim X : exist X -> hexists (fun a => a ∈ X * P a).
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - contradiction.
    - intros a Pa.
      apply (tr(a;(tr idpath,Pa))).
    - intros X1 X2 HX1 HX2 Hex.
      strip_truncations.
      destruct Hex.
      * specialize (HX1 t).
        strip_truncations.
        destruct HX1 as [a [Hin Pa]].
        refine (tr(a;(_,Pa))).
        apply (tr(inl Hin)).
      * specialize (HX2 t).
        strip_truncations.
        destruct HX2 as [a [Hin Pa]].
        refine (tr(a;(_,Pa))).
        apply (tr(inr Hin)).
  Defined.  

  Context `{forall a, Decidable (P a)}.

  Global Instance all_decidable : (forall X, Decidable (all X)).
  Proof.
    hinduction ; try (apply _) ; try (intros ; apply path_ishprop).
  Defined.

  Global Instance exist_decidable : (forall X, Decidable (exist X)).
  Proof.
    hinduction ; try (apply _) ; try (intros ; apply path_ishprop).
  Defined.
End quantifiers.

Section simple_example.
  Context `{Univalence}.

  Definition P : nat -> hProp := fun n => BuildhProp(n = n).
  Definition X : FSet nat := {|0|} ∪ {|1|}.

  Definition simple_example : all P X.
  Proof.
    refine (from_squash (all P X)).
    compute.
    apply tt.
  Defined.
End simple_example.