(** Interface for lattices and join semilattices. *)
Require Import HoTT.

Section binary_operation.
  Definition operation (A : Type) := A -> A -> A.
  
  Variable (A : Type)
           (f : operation A).

  Class Commutative :=
    commutative : forall x y, f x y = f y x.

  Class Associative :=
    associativity : forall x y z, f (f x y) z = f x (f y z).

  Class Idempotent :=
    idempotency : forall x, f x x = x.

  Variable g : operation A.

  Class Absorption :=
    absorb : forall x y, f x (g x y) = x.

  Variable (n : A).

  Class NeutralL :=
    neutralityL : forall x, f n x = x.

  Class NeutralR :=
    neutralityR : forall x, f x n = x.
End binary_operation.

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

Section lattice_operations.
  Variable (A : Type).

  Class maximum :=
    max_L : operation A.

  Class minimum :=
    min_L : operation A.

  Class bottom :=
    empty : A.
End lattice_operations.

Arguments max_L {_} {_} _.
Arguments min_L {_} {_} _.
Arguments empty {_}.

Section JoinSemiLattice.
  Variable A : Type.
  Context {max_L : maximum A} {empty_L : bottom A}.

  Class JoinSemiLattice :=
    {
      commutative_max_js :> Commutative max_L ;
      associative_max_js :> Associative max_L ;
      idempotent_max_js :> Idempotent max_L ;
      neutralL_max_js :> NeutralL max_L empty_L ;
      neutralR_max_js :> NeutralR max_L empty_L ;
    }.
End JoinSemiLattice.

Arguments JoinSemiLattice _ {_} {_}.

Create HintDb joinsemilattice_hints.
Hint Resolve associativity : joinsemilattice_hints.
Hint Resolve (associativity _ _ _)^ : joinsemilattice_hints.
Hint Resolve commutative : joinsemilattice_hints.
Hint Resolve idempotency : joinsemilattice_hints.
Hint Resolve neutralityL : joinsemilattice_hints.
Hint Resolve neutralityR : joinsemilattice_hints.

Section Lattice.
  Variable A : Type.
  Context {max_L : maximum A} {min_L : minimum A} {empty_L : bottom A}.

  Class Lattice :=
    {
      commutative_min :> Commutative min_L ;
      commutative_max :> Commutative max_L ;
      associative_min :> Associative min_L ;
      associative_max :> Associative max_L ;
      idempotent_min :> Idempotent min_L ;
      idempotent_max :> Idempotent max_L ;
      neutralL_max :> NeutralL max_L empty_L ;
      neutralR_max :> NeutralR max_L empty_L ;
      absorption_min_max :> Absorption min_L max_L ;
      absorption_max_min :> Absorption max_L min_L
    }.
End Lattice.

Arguments Lattice _ {_} {_} {_}.

Create HintDb lattice_hints.
Hint Resolve associativity : lattice_hints.
Hint Resolve (associativity _ _ _)^ : lattice_hints.
Hint Resolve commutative : lattice_hints.
Hint Resolve absorb : lattice_hints.
Hint Resolve idempotency : lattice_hints.
Hint Resolve neutralityL : lattice_hints.
Hint Resolve neutralityR : lattice_hints.