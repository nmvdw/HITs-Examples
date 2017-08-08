Require Import HoTT.
Require Import FSets.

Section interface.
  Context `{Univalence}.
  Variable (T : Type -> Type)
           (f : forall A, T A -> FSet A).
  Context `{hasMembership T, hasEmpty T, hasSingleton T, hasUnion T, hasComprehension T}.

  Class sets :=
    {
      f_empty : forall A, f A empty = ∅ ;
      f_singleton : forall A a, f A (singleton a) = {|a|};
      f_union : forall A X Y, f A (union X Y) = (f A X) ∪ (f A Y);
      f_filter : forall A ϕ X, f A (filter ϕ X) = comprehension ϕ (f A X);
      f_member : forall A a X, member a X = a ∈ (f A X)
    }.
End interface.

Section properties.
  Context `{Univalence}.
  Variable (T : Type -> Type) (f : forall A, T A -> FSet A).
  Context `{sets T f}.

  Definition set_eq : forall A, T A -> T A -> hProp :=
    fun A X Y => (BuildhProp (f A X = f A Y)).

  Definition set_subset : forall A, T A -> T A -> hProp :=
    fun A X Y => (f A X) ⊆ (f A Y).

  Ltac reduce :=
    intros ;
    repeat (rewrite (f_empty _ _)
         || rewrite ?(f_singleton _ _)
         || rewrite ?(f_union _ _)
         || rewrite ?(f_filter _ _)
         || rewrite ?(f_member _ _)).

  Definition empty_isIn : forall (A : Type) (a : A),
    member a empty = False_hp.
  Proof.
    by reduce.
  Defined.

  Definition singleton_isIn : forall (A : Type) (a b : A),
    member a (singleton b) = merely (a = b).
  Proof.
    by reduce.
  Defined.

  Definition union_isIn : forall (A : Type) (a : A) (X Y : T A),
    member a (union X Y) = lor (member a X) (member a Y).
  Proof.
    by reduce.
  Defined.

  Definition filter_isIn : forall (A : Type) (a : A) (ϕ : A -> Bool) (X : T A),
    member a (filter ϕ X) = if ϕ a then member a X else False_hp.
  Proof.
    reduce.
    apply properties.comprehension_isIn.
  Defined.

  Definition reflect_eq : forall (A : Type) (X Y : T A),
    f A X = f A Y -> set_eq A X Y.
  Proof. done. Defined.

  Definition reflect_subset : forall (A : Type) (X Y : T A),
    subset (f A X) (f A Y) -> set_subset A X Y.
  Proof. done. Defined.

  Hint Unfold set_eq set_subset.

  Ltac simplify := intros ; autounfold in * ; apply reflect_eq ; reduce.

  Definition well_defined_union : forall (A : Type) (X1 X2 Y1 Y2 : T A),
    set_eq A X1 Y1 -> set_eq A X2 Y2 -> set_eq A (union X1 X2) (union Y1 Y2).
  Proof.
    intros A X1 X2 Y1 Y2 HXY1 HXY2.
    simplify.
    by rewrite HXY1, HXY2.
  Defined.

  Definition well_defined_filter : forall (A : Type) (ϕ : A -> Bool) (X Y : T A),
    set_eq A X Y -> set_eq A (filter ϕ X) (filter ϕ Y).
  Proof.    
    intros A ϕ X Y HXY.
    simplify.
    by rewrite HXY.
  Defined.
  
  Lemma union_comm : forall A (X Y : T A),
    set_eq A (union X Y) (union Y X).
  Proof.
    simplify.
    apply comm.
  Defined.

End properties.
