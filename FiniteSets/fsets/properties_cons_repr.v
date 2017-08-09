(* Properties of the operations on [FSetC A] *)
Require Import HoTT HitTactics.
Require Import representations.cons_repr.
From fsets Require Import operations_cons_repr.

Section properties.
  Context {A : Type}.

  Definition append_nl : forall (x: FSetC A), ∅ ∪ x = x
    := fun _ => idpath.

  Lemma append_nr : forall (x: FSetC A), x ∪ ∅ = x.
  Proof.
    hinduction; try (intros; apply set_path2).
    -  reflexivity.
    -  intros. apply (ap (fun y => a;;y) X).
  Defined.

  Lemma append_assoc {H: Funext}:
    forall (x y z: FSetC A), x ∪ (y ∪ z) = (x ∪ y) ∪ z.
  Proof.
    hinduction
    ; try (intros ; apply path_forall ; intro
           ; apply path_forall ; intro ;  apply set_path2).
    - reflexivity.
    - intros a x HR y z.
      specialize (HR y z).
      apply (ap (fun y => a;;y) HR).
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
    - intros. symmetry. apply append_nr.
    - intros a x1 HR x2.
      etransitivity.
      apply (ap (fun y => a;;y) (HR x2)).
      transitivity  ((x2 ∪ x1) ∪ (a;;∅)).
      + apply append_singleton.
      + etransitivity.
    	* symmetry. apply append_assoc.
    	* simple refine (ap (x2 ∪) (append_singleton _ _)^).
  Defined.

  Lemma singleton_idem: forall (a: A),
      {|a|} ∪ {|a|} = {|a|}.
  Proof.
    unfold singleton.
    intro.
    apply dupl.
  Defined.

End properties.
