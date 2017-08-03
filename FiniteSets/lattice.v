(* Typeclass for lattices *)
Require Import HoTT.

Section binary_operation.
  Variable A : Type.
  
  Definition operation := A -> A -> A.

  Class maximum :=
    max_L : operation.

  Class minimum :=
    min_L : operation.

  Class bottom :=
    empty : A.
End binary_operation.

Arguments max_L {_} {_} _.
Arguments min_L {_} {_} _.
Arguments empty {_}.

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
Hint Resolve commutative : lattice_hints.
Hint Resolve absorb : lattice_hints.
Hint Resolve idempotency : lattice_hints.
Hint Resolve neutralityL : lattice_hints.
Hint Resolve neutralityR : lattice_hints.

Section BoolLattice.

  Ltac solve_bool :=
    let x := fresh in
    repeat (intro x ; destruct x) 
    ; compute
    ; auto
    ; try contradiction.

  Instance maximum_bool : maximum Bool := orb.
  Instance minimum_bool : minimum Bool := andb.
  Instance bottom_bool : bottom Bool := false.
  
  Global Instance lattice_bool : Lattice Bool.
  Proof.
    split ; solve_bool.
  Defined.
  
  Definition and_true : forall b, andb b true = b.
  Proof.
    solve_bool.
  Defined.

  Definition and_false : forall b, andb b false = false.
  Proof.
    solve_bool.
  Defined.

  Definition dist₁ : forall b₁ b₂ b₃,
      andb b₁ (orb b₂ b₃) = orb (andb b₁ b₂) (andb b₁ b₃).
  Proof.
    solve_bool.
  Defined.

  Definition dist₂ : forall b₁ b₂ b₃,
      orb b₁ (andb b₂ b₃) = andb (orb b₁ b₂) (orb b₁ b₃).
  Proof.
    solve_bool.
  Defined.

  Definition max_min : forall b₁ b₂,
      orb (andb b₁ b₂) b₁ = b₁.
  Proof.
    solve_bool.
  Defined.
  
End BoolLattice.

Section fun_lattice.
  Context {A B : Type}.
  Context `{Lattice B}.
  Context `{Funext}.

  Global Instance max_fun : maximum (A -> B) :=
    fun (f g : A -> B) (a : A) => max_L0 (f a) (g a).

  Global Instance min_fun : minimum (A -> B) :=
    fun (f g : A -> B) (a : A) => min_L0 (f a) (g a).

  Global Instance bot_fun : bottom (A -> B)
    := fun _ => empty_L.

  Ltac solve_fun :=
    compute ; intros ; apply path_forall ; intro ;
    eauto with lattice_hints typeclass_instances.

  Global Instance lattice_fun : Lattice (A -> B).
  Proof.
    split ; solve_fun.
  Defined.
  
End fun_lattice.

Section sub_lattice.
  Context {A : Type} {P : A -> hProp}.
  Context `{Lattice A}.
  Context {Hmax : forall x y, P x -> P y -> P (max_L0 x y)}.
  Context {Hmin : forall x y, P x -> P y -> P (min_L0 x y)}.
  Context {Hbot : P empty_L}.

  Definition AP : Type := sig P.
  
  Instance botAP : bottom AP := (empty_L ; Hbot).

  Instance maxAP : maximum AP :=
    fun x y =>
      match x, y with
      | (a ; pa), (b ; pb) => (max_L0 a b ; Hmax a b pa pb)
      end.

  Instance minAP : minimum AP :=
    fun x y =>
      match x, y with
      | (a ; pa), (b ; pb) => (min_L0 a b ; Hmin a b pa pb)
      end.

  Instance hprop_sub : forall c, IsHProp (P c).
  Proof.
    apply _.
  Defined.

  Ltac solve_sub :=
    let x := fresh in
    repeat (intro x ; destruct x) 
    ; simple refine (path_sigma _ _ _ _ _)
    ; simpl
    ; try (apply hprop_sub)
    ; eauto 3 with lattice_hints typeclass_instances.
  
  Global Instance lattice_sub : Lattice AP.
  Proof.
    split ; solve_sub.
  Defined.
  
End sub_lattice.

Create HintDb bool_lattice_hints.
Hint Resolve associativity : bool_lattice_hints.
Hint Resolve commutative : bool_lattice_hints.
Hint Resolve absorb : bool_lattice_hints.
Hint Resolve idempotency : bool_lattice_hints.
Hint Resolve neutralityL : bool_lattice_hints.
Hint Resolve neutralityR : bool_lattice_hints.

Hint Resolve
     associativity
     and_true and_false
     dist₁ dist₂ max_min
 : bool_lattice_hints.
