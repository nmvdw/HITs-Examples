Require Import HoTT HitTactics.
Require Import cons_repr operations_decidable properties_decidable definition.

Section Operations.
  Variable A : Type.
  Context {A_deceq : DecidablePaths A}.
  
  Fixpoint member (l : list A) (a : A) : Bool :=
    match l with
    | nil => false
    | cons b l => if (dec (a = b)) then true else member l a
    end.

  Fixpoint append (l1 l2 : list A) :=
    match l1 with
    | nil => l2
    | cons a l => cons a (append l l2)
    end.

  Definition empty : list A := nil.

  Definition singleton (a : A) : list A := cons a nil.

  Fixpoint filter (ϕ : A -> Bool) (l : list A) : list A :=
    match l with
    | nil => nil
    | cons a l => if ϕ a then cons a (filter ϕ l) else filter ϕ l
    end.

  Fixpoint cardinality (l : list A) : nat :=
    match l with
    | nil => 0
    | cons a l => if member l a then cardinality l else 1 + cardinality l
    end.

End Operations.

Arguments nil {_}.
Arguments cons {_} _ _.
Arguments member {_} {_} _ _.
Arguments singleton {_} _.
Arguments append {_} _ _.
Arguments empty {_}.
Arguments filter {_} _ _.
Arguments cardinality {_} {_} _.

Section ListToSet.
  Variable A : Type.
  Context {A_deceq : DecidablePaths A} `{Univalence}.
  
  Fixpoint list_to_setC (l : list A) : FSetC A :=
    match l with
    | nil => Nil
    | cons a l => Cns a (list_to_setC l)
    end.

  Definition list_to_set (l : list A) := FSetC_to_FSet(list_to_setC l).
    
  Lemma list_to_setC_surj : forall X : FSetC A, Trunc (-1) ({l : list A & list_to_setC l = X}).
  Proof.
    hrecursion ; try (intros ; apply hprop_allpath ; apply (istrunc_truncation (-1) _)).
    - apply tr ; exists nil ; cbn. reflexivity.
    - intros a x P.
      simple refine (Trunc_rec _ P).
      intros [l Q].
      apply tr. 
      exists (cons a l).
      simpl.
      apply (ap (fun y => a;;y) Q).
  Defined.

  Lemma member_isIn (l : list A) (a : A) :
    member l a = isIn_b a (FSetC_to_FSet (list_to_setC l)).
  Proof.
    induction l ; cbn in *.
    - reflexivity.
    - destruct (dec (a = a0)) ; cbn.
      * rewrite ?p. simplify_isIn. reflexivity.
      * rewrite IHl. simplify_isIn. rewrite L_isIn_b_false ; auto.
  Defined.

  Lemma append_FSetCappend (l1 l2 : list A) :
    list_to_setC (append l1 l2) = FSetC.append (list_to_setC l1) (list_to_setC l2).
  Proof.
    induction l1 ; simpl in *.
    - reflexivity.
    - apply (ap (fun y => a ;; y) IHl1).
  Defined.

  Lemma append_FSetappend (l1 l2 : list A) :
    list_to_set (append l1 l2) = U (list_to_set l1) (list_to_set l2).
  Proof.
    induction l1 ; cbn in *.
    - symmetry. apply nl.
    - rewrite <- assoc.
      refine (ap (fun y => U {|a|} y) _).
      rewrite <- append_union.
      rewrite <- append_FSetCappend.
      reflexivity.
  Defined.

  Lemma empty_empty : list_to_set empty = E.
  Proof.
    reflexivity.
  Defined.

  Lemma filter_comprehension (l : list A) (ϕ : A -> Bool) :
    list_to_set (filter ϕ l) = comprehension ϕ (list_to_set l).
  Proof.
    induction l ; cbn in *.
    - reflexivity.
    - destruct (ϕ a) ; cbn in * ; unfold list_to_set in IHl.
      * refine (ap (fun y => U {|a|} y) _).
        apply IHl.
      * rewrite nl.
        apply IHl.
  Defined.
  
  Lemma length_sizeC (l : list A) :
    cardinality l = cons_repr.length (list_to_setC l).
  Proof.
    induction l.
    - cbn.
      reflexivity.
    - simpl.
      rewrite IHl.
      rewrite member_isIn.
      reflexivity.
  Defined.

  Lemma length_size (l : list A) :
    cardinality l = length_FSet (list_to_set l).
  Proof.
    unfold length_FSet.
    unfold list_to_set.
    rewrite repr_iso_id_r.
    apply length_sizeC.
  Defined.

  Lemma singleton_single (a : A) :
    list_to_set (singleton a) = L a.
  Proof.
    cbn.
    apply nr.
  Defined.    

End ListToSet.