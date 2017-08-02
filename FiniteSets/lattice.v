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
      neutralL_max :> NeutralL max empty ;
      neutralR_max :> NeutralR max empty ;
      absorption_min_max :> Absorption min max ;
      absorption_max_min :> Absorption max min
    }.
                     
End Lattice.

Arguments Lattice {_} _ _ _.


Section BoolLattice.

  Ltac solve_bool :=
    let x := fresh in
    repeat (intro x ; destruct x) 
    ; compute
    ; auto
    ; try contradiction.

  Instance orb_com : Commutative orb.
  Proof.
    solve_bool.
  Defined.

  Instance andb_com : Commutative andb.
  Proof.
    solve_bool.
  Defined.

  Instance orb_assoc : Associative orb.
  Proof.
    solve_bool.
  Defined.

  Instance andb_assoc : Associative andb.
  Proof.
    solve_bool.
  Defined.

  Instance orb_idem : Idempotent orb.
  Proof.
    solve_bool.
  Defined.

  Instance andb_idem : Idempotent andb.
  Proof.
    solve_bool.
  Defined.

  Instance orb_nl : NeutralL orb false.
  Proof.
    solve_bool.
  Defined.

  Instance orb_nr : NeutralR orb false.
  Proof.
    solve_bool.
  Defined.

  Instance bool_absorption_orb_andb : Absorption orb andb.
  Proof.
    solve_bool.
  Defined.

  Instance bool_absorption_andb_orb : Absorption andb orb.
  Proof.
    solve_bool.
  Defined.
  
  Global Instance lattice_bool : Lattice andb orb false :=
    { commutative_min := _ ;
      commutative_max := _ ;
      associative_min := _ ;
      associative_max := _ ;
      idempotent_min := _ ;
      idempotent_max := _ ;
      neutralL_max := _ ;
      neutralR_max := _ ;
      absorption_min_max := _ ;
      absorption_max_min := _
  }.

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
  Context {A B : Type} {maxB minB : B -> B -> B} {botB : B}.
  Context `{Lattice B minB maxB botB}.
  Context `{Funext}.

  Definition max_fun (f g : (A -> B)) (a : A) : B
    := maxB (f a) (g a).

  Definition min_fun (f g : (A -> B)) (a : A) : B
    := minB (f a) (g a).

  Definition bot_fun (a : A) : B
    := botB.

  Hint Unfold max_fun min_fun bot_fun.

  Ltac solve_fun := compute ; intros ; apply path_forall ; intro.
  
  Instance max_fun_com : Commutative max_fun.
  Proof.
    solve_fun.
    refine (commutative_max _ _ _ _ _ _).
  Defined.

  Instance min_fun_com : Commutative min_fun.
  Proof.
    solve_fun.
    refine (commutative_min _ _ _ _ _ _).
  Defined.

  Instance max_fun_assoc : Associative max_fun.
  Proof.
    solve_fun.
    refine (associative_max _ _ _ _ _ _ _).
  Defined.

  Instance min_fun_assoc : Associative min_fun.
  Proof.
    solve_fun.
    refine (associative_min _ _ _ _ _ _ _).
  Defined.

  Instance max_fun_idem : Idempotent max_fun.
  Proof.
    solve_fun.
    refine (idempotent_max _ _ _ _ _).
  Defined.

  Instance min_fun_idem : Idempotent min_fun.
  Proof.
    solve_fun.
    refine (idempotent_min _ _ _ _ _).
  Defined.

  Instance max_fun_nl : NeutralL max_fun bot_fun.
  Proof.
    solve_fun.
    simple refine (neutralL_max _ _ _ _ _).
  Defined.

  Instance max_fun_nr : NeutralR max_fun bot_fun.
  Proof.
    solve_fun.
    simple refine (neutralR_max _ _ _ _ _).
  Defined.

  Instance absorption_max_fun_min_fun : Absorption max_fun min_fun.
  Proof.
    solve_fun.
    simple refine (absorption_max_min _ _ _ _ _ _).
  Defined.

  Instance absorption_min_fun_max_fun : Absorption min_fun max_fun.
  Proof.
    solve_fun.
    simple refine (absorption_min_max _ _ _ _ _ _).
  Defined.
  
  Global Instance lattice_fun : Lattice min_fun max_fun bot_fun :=
    { commutative_min := _ ;
      commutative_max := _ ;
      associative_min := _ ;
      associative_max := _ ;
      idempotent_min := _ ;
      idempotent_max := _ ;
      neutralL_max := _ ;
      neutralR_max := _ ;
      absorption_min_max := _ ;
      absorption_max_min := _
  }.
End fun_lattice.

Section sub_lattice.
  Context {A : Type} {P : A -> hProp} {maxA minA : A -> A -> A} {botA : A}.
  Context {Hmax : forall x y, P x -> P y -> P (maxA x y)}.
  Context {Hmin : forall x y, P x -> P y -> P (minA x y)}.
  Context {Hbot : P botA}.
  Context `{Lattice A minA maxA botA}.

  Definition AP : Type := sig P.
  
  Definition botAP : AP := (botA ; Hbot).

  Definition maxAP (x y : AP) : AP :=
    match x with
    | (a ; pa) => match y with
                  | (b ; pb) => (maxA a b ; Hmax a b pa pb)
                  end
    end.

  Definition minAP (x y : AP) : AP :=
    match x with
    | (a ; pa) => match y with
                  | (b ; pb) => (minA a b ; Hmin a b pa pb)
                  end
    end.

  Hint Unfold maxAP minAP botAP.

  Instance hprop_sub : forall c, IsHProp (P c).
  Proof.
    apply _.
  Defined.

  Ltac solve_sub :=
    let x := fresh in
    repeat (intro x ; destruct x) 
    ; simple refine (path_sigma _ _ _ _ _) ; try (apply hprop_sub).
  
  Instance max_sub_com : Commutative maxAP.
  Proof.
    solve_sub.
    refine (commutative_max _ _ _ _ _ _).
  Defined.
  
  Instance min_sub_com : Commutative minAP.
  Proof.
    solve_sub.
    refine (commutative_min _ _ _ _ _ _).
  Defined.

  Instance max_sub_assoc : Associative maxAP.
  Proof.
    solve_sub.
    refine (associative_max _ _ _ _ _ _ _).
  Defined.

  Instance min_sub_assoc : Associative minAP.
  Proof.
    solve_sub.
    refine (associative_min _ _ _ _ _ _ _).
  Defined.

  Instance max_sub_idem : Idempotent maxAP.
  Proof.
    solve_sub.
    refine (idempotent_max _ _ _ _ _).
  Defined.

  Instance min_sub_idem : Idempotent minAP.
  Proof.
    solve_sub.
    refine (idempotent_min _ _ _ _ _).
  Defined.

  Instance max_sub_nl : NeutralL maxAP botAP.
  Proof.
    solve_sub.
    simple refine (neutralL_max _ _ _ _ _).
  Defined.

  Instance max_sub_nr : NeutralR maxAP botAP.
  Proof.
    solve_sub.
    simple refine (neutralR_max _ _ _ _ _).
  Defined.

  Instance absorption_max_sub_min_sub : Absorption maxAP minAP.
  Proof.
    solve_sub.
    simple refine (absorption_max_min _ _ _ _ _ _).
  Defined.

  Instance absorption_min_sub_max_sub : Absorption minAP maxAP.
  Proof.
    solve_sub.
    simple refine (absorption_min_max _ _ _ _ _ _).
  Defined.
  
  Global Instance lattice_sub : Lattice minAP maxAP botAP :=
    { commutative_min := _ ;
      commutative_max := _ ;
      associative_min := _ ;
      associative_max := _ ;
      idempotent_min := _ ;
      idempotent_max := _ ;
      neutralL_max := _ ;
      neutralR_max := _ ;
      absorption_min_max := _ ;
      absorption_max_min := _
  }.

End sub_lattice.

Hint Resolve
     orb_com andb_com orb_assoc andb_assoc orb_idem andb_idem orb_nl orb_nr
     bool_absorption_orb_andb bool_absorption_andb_orb and_true and_false
     dist₁ dist₂ max_min
 : bool_lattice_hints.
