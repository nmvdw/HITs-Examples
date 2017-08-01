(* Typeclass for lattices *)
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
      neutralL_min :> NeutralL max empty ;
      neutralR_min :> NeutralR max empty ;
      absorption_min_max :> Absorption min max ;
      absorption_max_min :> Absorption max min
    }.
                     
End Lattice.

Arguments Lattice {_} _ _ _.


Section BoolLattice.

  Ltac solve :=
    let x := fresh in
    repeat (intro x ; destruct x) 
    ; compute
    ; auto
    ; try contradiction.

  Instance orb_com : Commutative orb.
  Proof.
    solve.
  Defined.

  Instance andb_com : Commutative andb.
  Proof.
    solve.
  Defined.

  Instance orb_assoc : Associative orb.
  Proof.
    solve.
  Defined.

  Instance andb_assoc : Associative andb.
  Proof.
    solve.
  Defined.

  Instance orb_idem : Idempotent orb.
  Proof.
    solve.
  Defined.

  Instance andb_idem : Idempotent andb.
  Proof.
    solve.
  Defined.

  Instance orb_nl : NeutralL orb false.
  Proof.
    solve.
  Defined.

  Instance orb_nr : NeutralR orb false.
  Proof.
    solve.
  Defined.

  Instance bool_absorption_orb_andb : Absorption orb andb.
  Proof.
    solve.
  Defined.

  Instance bool_absorption_andb_orb : Absorption andb orb.
  Proof.
    solve.
  Defined.
  
  Global Instance lattice_bool : Lattice andb orb false :=
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

  Definition and_true : forall b, andb b true = b.
  Proof.
    solve.
  Defined.

  Definition and_false : forall b, andb b false = false.
  Proof.
    solve.
  Defined.

  Definition dist₁ : forall b₁ b₂ b₃,
      andb b₁ (orb b₂ b₃) = orb (andb b₁ b₂) (andb b₁ b₃).
  Proof.
    solve.
  Defined.

  Definition dist₂ : forall b₁ b₂ b₃,
      orb b₁ (andb b₂ b₃) = andb (orb b₁ b₂) (orb b₁ b₃).
  Proof.
    solve.
  Defined.

  Definition max_min : forall b₁ b₂,
      orb (andb b₁ b₂) b₁ = b₁.
  Proof.
    solve.
  Defined.
  
End BoolLattice.

Hint Resolve
     orb_com andb_com orb_assoc andb_assoc orb_idem andb_idem orb_nl orb_nr
     bool_absorption_orb_andb bool_absorption_andb_orb and_true and_false
     dist₁ dist₂ max_min
 : bool_lattice_hints.
