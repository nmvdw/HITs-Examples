(** Some examples of lattices. *)
Require Import HoTT lattice_interface.

(** [Bool] is a lattice. *)
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

Create HintDb bool_lattice_hints.
Hint Resolve associativity : bool_lattice_hints.
Hint Resolve (associativity _ _ _)^ : bool_lattice_hints.
Hint Resolve commutativity : bool_lattice_hints.
Hint Resolve absorb : bool_lattice_hints.
Hint Resolve idempotency : bool_lattice_hints.
Hint Resolve neutralityL : bool_lattice_hints.
Hint Resolve neutralityR : bool_lattice_hints.

Hint Resolve
     associativity
     and_true and_false
     dist₁ dist₂ max_min
  : bool_lattice_hints.

(** If [B] is a lattice, then [A -> B] is a lattice. *)
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

(** If [A] is a lattice and [P] is closed under the lattice operations, then [Σ(x:A), P x] is a lattice. *)
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

Instance lor : maximum hProp := fun X Y => BuildhProp (Trunc (-1) (sum X Y)).

Delimit Scope logic_scope with L.
Notation "A ∨ B" := (lor A B) (at level 20, right associativity) : logic_scope.
Arguments lor _%L _%L.
Open Scope logic_scope.

Instance land : minimum hProp := fun X Y => BuildhProp (prod X Y).
Instance lfalse : bottom hProp := False_hp.

Notation "A ∧ B" := (land A B) (at level 20, right associativity) : logic_scope.
Arguments land _%L _%L.
Open Scope logic_scope.

(** [hProp] is a lattice. *)
Section hPropLattice.
  Context `{Univalence}.

  Local Ltac lor_intros :=
    let x := fresh in intro x
                      ; repeat (strip_truncations ; destruct x as [x | x]).

  Instance lor_commutative : Commutative lor.
  Proof.
    intros X Y.
    apply path_iff_hprop ; lor_intros
    ; apply tr ; auto.
  Defined.

  Instance land_commutative : Commutative land.
  Proof.
    intros X Y.
    apply path_hprop.
    apply equiv_prod_symm.
  Defined.

  Instance lor_associative : Associative lor.
  Proof.
    intros X Y Z.
    apply path_iff_hprop ; lor_intros
    ; apply tr ; auto
    ; try (left ; apply tr)
    ; try (right ; apply tr) ; auto.
  Defined.

  Instance land_associative : Associative land.
  Proof.
    intros X Y Z.
    symmetry.
    apply path_hprop.
    apply equiv_prod_assoc.
  Defined.

  Instance lor_idempotent : Idempotent lor.
  Proof.
    intros X.
    apply path_iff_hprop ; lor_intros
    ; try(refine (tr(inl _))) ; auto.
  Defined.

  Instance land_idempotent : Idempotent land.
  Proof.
    intros X.
    apply path_iff_hprop ; cbn.
    - intros [a b] ; apply a.
    - intros a ; apply (pair a a).
  Defined.

  Instance lor_neutrall : NeutralL lor lfalse.
  Proof.
    intros X.
    apply path_iff_hprop ; lor_intros ; try contradiction
    ; try (refine (tr(inr _))) ; auto.
  Defined.

  Instance lor_neutralr : NeutralR lor lfalse.
  Proof.
    intros X.
    apply path_iff_hprop ; lor_intros ; try contradiction
    ; try (refine (tr(inl _))) ; auto.
  Defined.

  Instance absorption_orb_andb : Absorption lor land.
  Proof.
    intros Z1 Z2.
    apply path_iff_hprop ; cbn.
    - intros X ; strip_truncations.
      destruct X as [Xx | [Xy1 Xy2]] ; assumption.
    - intros X.
      apply (tr (inl X)).
  Defined.

  Instance absorption_andb_orb : Absorption land lor.
  Proof.
    intros Z1 Z2.
    apply path_iff_hprop ; cbn.
    - intros [X Y] ; strip_truncations.
      assumption.
    - intros X.
      split.
      * assumption.
      * apply (tr (inl X)).
  Defined.

  Global Instance lattice_hprop : Lattice hProp :=
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
End hPropLattice.
