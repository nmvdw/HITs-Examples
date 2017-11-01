(* Implementation of [FSet A] using lists *)
Require Import HoTT HitTactics.
Require Import FSets set_interface kuratowski.length prelude dec_fset.

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
    list_to_set A (filter ϕ l) =  {| list_to_set A l | ϕ |}.
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
    list_to_set A (list_union _ l1 l2) = (list_to_set A l1) ∪ (list_to_set A l2).
  Proof.
    induction l1 ; simpl.
    - apply (nl _)^.
    - rewrite IHl1, assoc.
      reflexivity.
  Defined.

  Fixpoint reverse (l : list A) : list A :=
    match l with
    | nil => nil
    | cons a l => {|a|} ∪ (reverse l) ∪ {|a|}
    end.

  Lemma reverse_set (l : list A) :
    list_to_set A l = list_to_set A (reverse l).
  Proof.
    induction l ; simpl.
    - reflexivity.
    - rewrite IHl, append_union.
      simpl.
      symmetry.
      rewrite nr, comm, <- assoc, idem.
      apply comm.
  Defined.
    
End ListToSet.

Section lists_are_sets.
  Context `{Univalence}.

  Global Instance lists_sets : sets list list_to_set.
  Proof.
    split ; intros.
    - apply empty_empty.
    - apply singleton_single.
    - apply append_union.
    - apply filter_comprehension.
    - apply member_isIn.
  Defined.
End lists_are_sets.

Section refinement_examples.
  Context `{Univalence}.
  Context {A : Type}.

  Definition list_all (ϕ : A -> hProp) : list A -> hProp
    := refinement list list_to_set (all ϕ).

  Lemma list_all_set (ϕ : A -> hProp) (X : list A)
    : list_all ϕ X = all ϕ (list_to_set A X).
  Proof.
    induction X ; try reflexivity.
  Defined.

  Lemma list_all_intro (X : list A) (ϕ : A -> hProp)
    : forall (HX : forall a, a ∈ X -> ϕ a), list_all ϕ X.
  Proof.
    rewrite list_all_set.
    intros H1.
    assert (forall (a : A), a ∈ (list_to_set A X) -> ϕ a) as H2.
    {
      intros a H3.
      rewrite <- (member_isIn A a X) in H3.
      apply (H1 a H3).
    }
    apply (all_intro _ _ H2).
  Defined.

  Lemma list_all_elim (X : list A) (ϕ : A -> hProp) a
    : list_all ϕ X -> (a ∈ X) -> ϕ a.
  Proof.
    rewrite list_all_set, (member_isIn A a X).
    apply all_elim.
  Defined.

  Definition list_exist (ϕ : A -> hProp) : list A -> hProp
    := refinement list list_to_set (exist ϕ).
  
  Lemma list_exist_set (ϕ : A -> hProp) (X : list A)
    : list_exist ϕ X = exist ϕ (list_to_set A X).
  Proof.
    induction X ; try reflexivity.
  Defined.

  Lemma listexist_intro (X : list A) (ϕ : A -> hProp) a
    : a ∈ X -> ϕ a -> list_exist ϕ X.
  Proof.
    rewrite list_exist_set, (member_isIn A a X).
    apply exist_intro.
  Defined.

  Lemma exist_elim (X : list A) (ϕ : A -> hProp)
    : list_exist ϕ X -> hexists (fun a => a ∈ X * ϕ a)%type.
  Proof.
    rewrite list_exist_set.
    assert (hexists (fun a : A => a ∈ (list_to_set A X) * ϕ a)
            -> hexists (fun a : A => a ∈ X * ϕ a))%type
      as H2.
    {
      intros H1.
      strip_truncations.
      destruct H1 as [a H1].
      rewrite <- (member_isIn A a X) in H1.
      refine (tr(a;H1)).
    }
    intros H1.
    apply (H2 (exist_elim _ _ H1)).
  Defined.

  Context `{MerelyDecidablePaths A}.

  Global Instance dec_memb a (l : list A) : Decidable (a ∈ l).
  Proof.
    induction l as [ | a0 l] ; simpl.
    - apply _.
    - unfold Decidable.
      destruct IHl as [t | p].
      * apply (inl(tr(inr t))).
      * destruct (H0 a a0) as [t | p'].
        ** left.
           strip_truncations.
           apply (tr(inl t)).
        ** refine (inr(fun n => _)).
           strip_truncations.
           destruct n as [n1 | n2].
           *** apply (p' (tr n1)).
           *** apply (p n2).
  Defined.
  
  Global Instance dec_memb_list : hasMembership_decidable (list A) A.
  Proof.
    intros a l.
    destruct (dec (a ∈ l)).
    - apply true.
    - apply false.
  Defined.

  Lemma fset_list_memb a (l : list A) : a ∈_d (list_to_set A l) = a ∈_d l.
  Proof.
    unfold member_dec, dec_memb_list, fset_member_bool.
    destruct (dec a ∈ (list_to_set A l)), (dec a ∈ l) ; try reflexivity.
    - contradiction n.
      rewrite <- (f_member _ list_to_set) in t.
      apply t.
    - contradiction n.
      rewrite (f_member _ list_to_set) in t.
      apply t.
  Defined.
        
  Definition set_length : list A -> nat
    := refinement list list_to_set length.

  Definition set_length_nil : set_length nil = 0 := idpath.

  Definition set_length_cons a l
    : set_length (cons a l) = if (a ∈_d l) then set_length l else S(set_length l).
  Proof.
    unfold set_length, refinement.
    simpl.
    rewrite length_compute, fset_list_memb.
    reflexivity.
  Defined.
End refinement_examples.
