(** Properties of the operations on [FSetC A] *)
Require Import HoTT HitTactics.
Require Import list_representation list_representation.operations.

Section properties.
  Context {A : Type}.

  Definition append_nl (x: FSetC A) : ∅ ∪ x = x
    := idpath.

  Lemma append_nr : forall (x: FSetC A), x ∪ ∅ = x.
  Proof.
    hinduction; try (intros; apply set_path2).
    - reflexivity.
    - intros. apply (ap (fun y => a;;y) X).
  Defined.

  Lemma append_assoc :
    forall (x y z: FSetC A), x ∪ (y ∪ z) = (x ∪ y) ∪ z.
  Proof.
    intros x y z.
    hinduction x ; try (intros ; apply path_ishprop).
    - cbn.
      reflexivity.
    - intros.
      cbn.
      f_ap.
  Defined.

  Lemma append_singleton: forall (a: A) (x: FSetC A),
      a ;; x = x ∪ (a ;; ∅).
  Proof.
    intro a. hinduction; try (intros; apply set_path2).
    - reflexivity.
    - intros b x HR. refine (_ @ _).
      + apply comm.
      + apply (ap (fun y => b ;; y) HR).
  Defined.

  Lemma append_comm {H: Funext}:
    forall (x1 x2: FSetC A), x1 ∪ x2 = x2 ∪ x1.
  Proof.
    hinduction ;  try (intros ; apply path_forall ; intro ; apply set_path2).
    - intros.
      apply (append_nr _)^.
    - intros a x1 HR x2.
      refine (ap (fun y => a;;y) (HR x2) @ _).
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
