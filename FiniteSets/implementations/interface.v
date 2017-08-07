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