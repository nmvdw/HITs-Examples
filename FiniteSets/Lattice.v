Require Import HoTT.

Definition operation (A : Type) := A -> A -> A.

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
    absrob : forall x y, f x (g x y) = x.

  Variable n : A.

  Class NeutralL :=
    neutralityL : forall x, f x n = x.

  Class NeutralR :=
    neutralityR : forall x, f n x = x.

End Defs.

Arguments Commutative {_} _.
Arguments Associative {_} _.
Arguments Idempotent {_} _.
Arguments NeutralL {_} _ _.
Arguments NeutralR {_} _ _.
Arguments Absorption {_} _ _.

Section Lattice.
  Variable A : Type.
  Variable min max : operation A.
  Variable empty : A.

  Class Lattice :=
    {
      commutative_min :> Commutative min ;
      commutative_max :> Commutative max ;
      associative_min :> Associative min ;
      associative_max :> Associative max ;
      idempotent_min :> Idempotent min ;
      idempotent_max :> Idempotent max ;
      neutralL_min :> NeutralL min empty ;
      neutralR_min :> NeutralR min empty ;
      absorption_min_max :> Absorption min max ;
      absorption_max_min :> Absorption max min
    }.
                     
End Lattice.

Arguments Lattice {_} _ _ _.


Section BoolLattice.

  Local Ltac solve :=
    let x := fresh in
    repeat (intro x ; destruct x) 
    ; compute
    ; auto
    ; try contradiction.

  Instance min_com : Commutative orb.
  Proof.
    solve.
  Defined.

  Instance max_com : Commutative andb.
  Proof.
    solve.
  Defined.

  Instance min_assoc : Associative orb.
  Proof.
    solve.
  Defined.

  Instance max_assoc : Associative andb.
  Proof.
    solve.
  Defined.

  Instance min_idem : Idempotent orb.
  Proof.
    solve.
  Defined.

  Instance max_idem : Idempotent andb.
  Proof.
    solve.
  Defined.

  Instance min_nl : NeutralL orb false.
  Proof.
    solve.
  Defined.

  Instance min_nr : NeutralR orb false.
  Proof.
    solve.
  Defined.

  Instance bool_absorption_min_max : Absorption orb andb.
  Proof.
    solve.
  Defined.

  Instance bool_absorption_max_min : Absorption andb orb.
  Proof.
    solve.
  Defined.
  
  Global Instance lattice_bool : Lattice orb andb false :=
  { commutative_min := _ ;
      commutative_max := _ ;
      associative_min := _ ;
      associative_max := _ ;
      idempotent_min := _ ;
      idempotent_max := _ ;
      neutralL_min := _ ;
      neutralR_min := _ ;
      absorption_min_max := _ ;
      absorption_max_min := _
  }.

End BoolLattice.

Hint Resolve
     min_com max_com min_assoc max_assoc min_idem max_idem min_nl min_nr
     bool_absorption_min_max bool_absorption_max_min
 : bool_lattice_hints.
