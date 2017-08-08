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
  Variable (T A : Type).
  
  Class hasMembership : Type :=
    member : A -> T -> hProp.

  Class hasMembership_decidable : Type :=
    member_dec : A -> T -> Bool.

  Class hasSubset : Type :=
    subset : T -> T -> hProp.

  Class hasSubset_decidable : Type :=
    subset_dec : T -> T -> Bool.

  Class hasEmpty : Type :=
    empty : T.

  Class hasSingleton : Type :=
    singleton : A -> T.
  
  Class hasUnion : Type :=
    union : T -> T -> T.

  Class hasIntersection : Type :=
    intersection : T -> T -> T.

  Class hasComprehension : Type :=
    filter : (A -> Bool) -> T -> T.
End structure.

Arguments member {_} {_} {_} _ _.
Arguments subset {_} {_} _ _.
Arguments member_dec {_} {_} {_} _ _.
Arguments subset_dec {_} {_} _ _.
Arguments empty {_} {_}.
Arguments singleton {_} {_} {_} _.
Arguments union {_} {_} _ _.
Arguments intersection {_} {_} _ _.
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
Infix  "⊆" := subset (at level 10, right associativity).
Infix "∈_d" := member_dec (at level 9, right associativity).
Infix  "⊆_d" := subset_dec (at level 10, right associativity).