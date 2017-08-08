(* Implementation of [FSet A] using lists *)
Require Import HoTT HitTactics.
Require Import FSets implementations.interface.

Section Operations.
  Context `{Univalence}.

  Global Instance list_empty A : hasEmpty (list A) := nil.

  Global Instance list_single A: hasSingleton (list A) A := fun a => cons a nil.
  
  Global Instance list_union A : hasUnion (list A).
  Proof.
    intros l1 l2.
    induction l1.
    * apply l2.
    * apply (cons a IHl1).
  Defined.

  Global Instance list_membership A : hasMembership (list A) A.
  Proof.
    intros a l.
    induction l as [ | b l IHl].
    - apply False_hp.
    - apply (hor (a = b) IHl).
  Defined.

  Global Instance list_comprehension A: hasComprehension (list A) A.
  Proof.
    intros ϕ l.
    induction l as [ | b l IHl].
    - apply nil.
    - apply (if ϕ b then cons b IHl else IHl).
  Defined.

  Fixpoint list_to_set A (l : list A) :  FSet A :=
    match l with
    | nil => ∅
    | cons a l => {|a|} ∪ (list_to_set A l)
    end.

End Operations.

Section ListToSet.
  Variable A : Type.
  Context `{Univalence}.

  Lemma member_isIn (a : A) (l : list A)  :
    member a l = a ∈ (list_to_set A l).
  Proof.
    induction l ; unfold member in * ; simpl in *.
    - reflexivity.
    - rewrite IHl.
      unfold hor, merely, lor.
      apply path_iff_hprop ; intros z ; strip_truncations ; destruct z as [z1 | z2].
      * apply (tr (inl (tr z1))).
      * apply (tr (inr z2)).
      * strip_truncations ; apply (tr (inl z1)).
      * apply (tr (inr z2)).
  Defined.
  
  Definition empty_empty : list_to_set A ∅ = ∅ := idpath.

  Lemma filter_comprehension (ϕ : A -> Bool) (l : list A)  :
    list_to_set A (filter ϕ l) =  {| list_to_set A l & ϕ |}.
  Proof.
    induction l ; cbn in *.
    - reflexivity.
    - destruct (ϕ a) ; cbn in * ; unfold list_to_set in IHl.
      * refine (ap (fun y => {|a|} ∪ y) _).
        apply IHl.
      * rewrite nl.
        apply IHl.
  Defined.
  
  Definition singleton_single (a : A) : list_to_set A (singleton a) = {|a|} :=
    nr {|a|}.

  Lemma append_union (l1 l2 : list A) :
    list_to_set A (union l1 l2) = (list_to_set A l1) ∪ (list_to_set A l2).
  Proof.
    induction l1 ; induction l2 ; cbn.
    - apply (nl _)^.
    - apply (nl _)^.
    - rewrite IHl1.
      apply assoc.
    - rewrite IHl1.
      cbn.
      apply assoc.
  Defined.
End ListToSet.

Section lists_are_sets.
  Context `{Univalence}.

  Instance lists_sets : sets list list_to_set.
  Proof.
    split ; intros.
    - apply empty_empty.
    - apply singleton_single.
    - apply append_union.
    - apply filter_comprehension.
    - apply member_isIn.
  Defined.
End lists_are_sets.
