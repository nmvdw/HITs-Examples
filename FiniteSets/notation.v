Require Import HoTT.

Section binary_operation.
  Variable A : Type.
  
  Definition operation := A -> A -> A.
End binary_operation.

Section Defs.
  Variable A : Type.
  Variable f : A -> A -> A.

  Class Commutative :=
    commutative : forall x y, f x y = f y x.

  Class Associative :=
    associativity : forall x y z, f (f x y) z = f x (f y z).

  Class Idempotent :=
    idempotency : forall x, f x x = x.

  Variable g : operation A.

  Class Absorption :=
    absorb : forall x y, f x (g x y) = x.

  Variable n : A.

  Class NeutralL :=
    neutralityL : forall x, f n x = x.

  Class NeutralR :=
    neutralityR : forall x, f x n = x.

End Defs.

Arguments Commutative {_} _.
Arguments Associative {_} _.
Arguments Idempotent {_} _.
Arguments NeutralL {_} _ _.
Arguments NeutralR {_} _ _.
Arguments Absorption {_} _ _.
Arguments commutative {_} {_} {_} _ _.
Arguments associativity {_} {_} {_} _ _ _.
Arguments idempotency {_} {_} {_} _.
Arguments neutralityL {_} {_} {_} {_} _.
Arguments neutralityR {_} {_} {_} {_} _.
Arguments absorb {_} {_} {_} {_} _ _.

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

  Class hasIntersection : Type :=
    intersection : forall A, T A -> T A -> T A.

  Class hasComprehension : Type :=
    filter : forall A, (A -> Bool) -> T A -> T A.
End structure.

Arguments member {_} {_} {_} _ _.
Arguments empty {_} {_} {_}.
Arguments singleton {_} {_} {_} _.
Arguments union {_} {_} {_} _ _.
Arguments filter {_} {_} {_} _ _.

Notation "∅" := empty.
Notation "{| x |}" :=  (singleton x).
Infix "∪" := union (at level 8, right associativity).
Notation "(∪)" := union (only parsing).
Notation "( X ∪)" := (union X) (only parsing).
Notation "( ∪ Y )" := (fun X => X ∪ Y) (only parsing).
Infix "∩" := intersection (at level 8, right associativity).
Notation "( ∩ )" := intersection (only parsing).
Notation "( X ∩ )" := (intersection X) (only parsing).
Notation "( ∩ Y )" := (fun X => X ∩ Y) (only parsing).
Notation "{| X & ϕ |}" := (filter ϕ X).
Infix "∈" := member (at level 9, right associativity).