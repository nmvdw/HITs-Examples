(** Properties of the operations on [FSetC A]. These are needed to prove that the 
    representations are isomorphic. *)
Require Import HoTT HitTactics.
Require Import list_representation list_representation.operations.

Section properties.
  Context {A : Type}.

  Definition append_nl (x: FSetC A) : ∅ ∪ x = x
    := idpath.

  Lemma append_nr : forall (x: FSetC A), x ∪ ∅ = x.
  Proof.
    hinduction; try (intros; apply path_ishprop).
    - reflexivity.
    - intros. apply (ap (fun y => a;;y) X).
  Defined.

  Lemma append_assoc :
    forall (x y z: FSetC A), x ∪ (y ∪ z) = (x ∪ y) ∪ z.
  Proof.
    intros x y z.
    hinduction x ; try (intros ; apply path_ishprop).
    - reflexivity.
    - intros.
      cbn.
      f_ap.
  Defined.

  Lemma append_singleton: forall (a: A) (x: FSetC A),
      a ;; x = x ∪ (a ;; ∅).
  Proof.
    intro a. hinduction; try (intros; apply path_ishprop).
    - reflexivity.
    - intros b x HR.
      refine (comm_s _ _ _ @ ap (fun y => b ;; y) HR).
  Defined.

  Lemma append_comm :
    forall (x1 x2: FSetC A), x1 ∪ x2 = x2 ∪ x1.
  Proof.
    intros x1 x2.
    hinduction x1 ;  try (intros ; apply path_ishprop).
    - intros.
      apply (append_nr _)^.
    - intros a x HR.
      refine (ap (fun y => a;;y) HR @ _).
      refine (append_singleton _ _ @ _).
      refine ((append_assoc _ _ _)^ @ _).
      refine (ap (x2 ∪) (append_singleton _ _)^).
  Defined.

  Lemma singleton_idem: forall (a: A),
      {|a|} ∪ {|a|} = {|a|}.
  Proof.
    intro.
    apply dupl.
  Defined.

End properties.
