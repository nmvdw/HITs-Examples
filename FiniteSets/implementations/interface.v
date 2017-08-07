Require Import HoTT.
Require Import FSets.

Section structure.
  Variable (T : Type -> Type).
  
  Class hasMembership : Type :=
    member : forall A : Type, A -> T A -> hProp.

  Class hasEmpty : Type :=
    empty : forall A, T A.

  Class hasSingleton : Type :=
    singleton : forall A, A -> T A.
  
  Class hasUnion : Type :=
    union : forall A, T A -> T A -> T A.

  Class hasComprehension : Type :=
    filter : forall A, (A -> Bool) -> T A -> T A.
End structure.

Arguments member {_} {_} {_} _ _.
Arguments empty {_} {_} {_}.
Arguments singleton {_} {_} {_} _.
Arguments union {_} {_} {_} _ _.
Arguments filter {_} {_} {_} _ _.

Section interface.
  Context `{Univalence}.
  Variable (T : Type -> Type)
           (f : forall A, T A -> FSet A).
  Context `{hasMembership T, hasEmpty T, hasSingleton T, hasUnion T, hasComprehension T}.

  Class sets :=
    {
      f_empty : forall A, f A empty = E ;
      f_singleton : forall A a, f A (singleton a) = L a;
      f_union : forall A X Y, f A (union X Y) = U (f A X) (f A Y);
      f_filter : forall A ϕ X, f A (filter ϕ X) = comprehension ϕ (f A X);
      f_member : forall A a X, member a X = isIn a (f A X)
    }.
End interface.

Section properties.
  Context `{Univalence}.
  Variable (T : Type -> Type) (f : forall A, T A -> FSet A).
  Context `{sets T f}.

  Definition set_eq : forall A, T A -> T A -> hProp := fun A X Y =>  (BuildhProp (f A X = f A Y)).

  Definition set_subset : forall A, T A -> T A -> hProp := fun A X Y => subset (f A X) (f A Y).

  Ltac reduce := intros ; repeat (rewrite ?(f_empty _ _) ; rewrite ?(f_singleton _ _) ;
                         rewrite ?(f_union _ _) ; rewrite ?(f_filter _ _) ;
                         rewrite ?(f_member _ _)).

  Definition empty_isIn : forall (A : Type) (a : A), member a empty = False_hp.
  Proof.
    reduce.
    reflexivity.
  Defined.

  Definition singleton_isIn : forall (A : Type) (a b : A),
      member a (singleton b) = BuildhProp (Trunc (-1) (a = b)).
  Proof.
    reduce.
    reflexivity.
  Defined.

  Definition union_isIn : forall (A : Type) (a : A) (X Y : T A),
      member a (union X Y) = lor (member a X) (member a Y).
  Proof.
    reduce.
    reflexivity.
  Defined.

  Definition filter_isIn : forall (A : Type) (a : A) (ϕ : A -> Bool) (X : T A),
      member a (filter ϕ X) = if ϕ a then member a X else False_hp.
  Proof.
    reduce.
    apply properties.comprehension_isIn.
  Defined.

  Definition reflect_eq : forall (A : Type) (X Y : T A),
      f A X = f A Y -> set_eq A X Y.
  Proof.
    auto.
  Defined.

  Definition reflect_subset : forall (A : Type) (X Y : T A),
      subset (f A X) (f A Y) -> set_subset A X Y.
  Proof.
    auto.
  Defined.

  Variable (A : Type).
  Context `{DecidablePaths A}.
  
  Lemma union_comm : forall (X Y : T A),
      set_eq A (union X Y) (union Y X).
  Proof.
    intros.
    apply reflect_eq.
    reduce.
    apply lattice_fset.
  Defined.

End properties.