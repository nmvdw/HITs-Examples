(** Some examples of lattices. *)
Require Export HoTT lattice_interface.

(** [Bool] is a lattice. *)
Section BoolLattice.
  Ltac solve_bool :=
    let x := fresh in
    repeat (intro x ; destruct x)
    ; compute
    ; auto
    ; try contradiction.

  Instance maximum_bool : Join Bool := orb.
  Instance minimum_bool : Meet Bool := andb.
  Instance bottom_bool : Bottom Bool := false.

  Global Instance boundedjoinsemilattice_bool : BoundedJoinSemiLattice Bool.
  Proof. repeat (split ; (apply _ || solve_bool)). Defined.
  Global Instance meetsemilattice_bool : MeetSemiLattice Bool.
  Proof. repeat (split ; (apply _ || solve_bool)). Defined.
  Global Instance boundedmeetsemilattice_bool : @BoundedSemiLattice Bool (⊓) true.
  Proof. repeat (split ; (apply _ || solve_bool)). Defined.
  Global Instance lattice_bool : Lattice Bool.
  Proof. split ; (apply _ || solve_bool). Defined.

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
(* Hint Resolve (associativity _ _ _)^ : bool_lattice_hints. *)
Hint Resolve commutativity : bool_lattice_hints.
Hint Resolve absorption : bool_lattice_hints.
Hint Resolve idempotency : bool_lattice_hints.
Hint Resolve left_identity : bool_lattice_hints.
Hint Resolve right_identity : bool_lattice_hints.

Hint Resolve
     associativity
     and_true and_false
     dist₁ dist₂ max_min
  : bool_lattice_hints.

(** If [B] is a lattice, then [A -> B] is a lattice. *)
Section fun_lattice.
  Context {A B : Type}.
  Context `{BJoin : Join B}.
  Context `{BMeet : Meet B}.
  Context `{@Lattice B BJoin BMeet}.
  Context `{Funext}.
  Context `{BBottom : Bottom B}.

  Global Instance bot_fun : Bottom (A -> B)
    := fun _ => ⊥.

  Global Instance join_fun : Join (A -> B) :=
    fun (f g : A -> B) (a : A) => (f a) ⊔ (g a).

  Global Instance meet_fun : Meet (A -> B) :=
    fun (f g : A -> B) (a : A) => (f a) ⊓ (g a).

  Ltac solve_fun :=
    compute ; intros ; apply path_forall ; intro ;
    eauto with lattice_hints typeclass_instances.

  Create HintDb test1.
  Lemma associativity_lat `{Lattice A} (x y z : A) :
    x ⊓ (y ⊓ z) = x ⊓ y ⊓ z.
  Proof. apply associativity. Defined.
  Hint Resolve associativity : test1.
  Hint Resolve associativity_lat : test1.

  Global Instance lattice_fun : Lattice (A -> B).
  Proof.
    repeat (split; try (apply _)).
    eauto with test1.
    (* TODO *)
    all: solve_fun.
    apply associativity.
    apply commutativity.
    apply idempotency. apply _.
    apply associativity.
    apply commutativity.
    apply idempotency. apply _.    
  Defined.

  Global Instance boundedjoinsemilattice_fun
   `{@BoundedJoinSemiLattice B BJoin BBottom} :
    BoundedJoinSemiLattice (A -> B).
  Proof.
    repeat split; try apply _; try solve_fun.
  Defined.
End fun_lattice.

(** If [A] is a lattice and [P] is closed under the lattice operations, then [Σ(x:A), P x] is a lattice. *)
Section sub_lattice.
  Context {A : Type} {P : A -> hProp}.
  Context `{Lattice A}.
  Context `{Bottom A}.
  Context {Hmax : forall x y, P x -> P y -> P (x ⊔ y)}.
  Context {Hmin : forall x y, P x -> P y -> P (x ⊓ y)}.
  Context {Hbot : P ⊥}.

  Definition AP : Type := sig P.

  Instance botAP : Bottom AP.
  Proof. refine (⊥ ↾ _). apply Hbot. Defined.

  Instance maxAP : Join AP :=
    fun x y =>
      match x, y with
      | (a ; pa), (b ; pb) => (a ⊔ b ; Hmax a b pa pb)
      end.

  Instance minAP : Meet AP :=
    fun x y =>
      match x, y with
      | (a ; pa), (b ; pb) => (a ⊓ b ; Hmin a b pa pb)
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
    repeat (split ; try (apply _ || solve_sub)).
    apply associativity.
    apply commutativity.
    apply idempotency. apply _.
    apply associativity.
    apply commutativity.
    apply idempotency. apply _.
  Defined.
End sub_lattice.

Instance lor : Join hProp := fun X Y => BuildhProp (Trunc (-1) (sum X Y)).

Delimit Scope logic_scope with L.
Notation "A ∨ B" := (lor A B) (at level 20, right associativity) : logic_scope.
Arguments lor _%L _%L.
Open Scope logic_scope.

Instance land : Meet hProp := fun X Y => BuildhProp (prod X Y).
Instance lfalse : Bottom hProp := False_hp.

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
    symmetry.
    apply equiv_prod_assoc.
  Defined.

  Instance lor_idempotent : BinaryIdempotent lor.
  Proof.
    intros X.
    apply path_iff_hprop ; lor_intros
    ; try(refine (tr(inl _))) ; auto.
  Defined.

  Instance land_idempotent : BinaryIdempotent land.
  Proof.
    intros X.
    apply path_iff_hprop ; cbn.
    - intros [a b] ; apply a.
    - intros a ; apply (pair a a).
  Defined.

  Instance lor_neutrall : LeftIdentity lor lfalse.
  Proof.
    intros X.
    apply path_iff_hprop ; lor_intros ; try contradiction
    ; try (refine (tr(inr _))) ; auto.
  Defined.

  Instance lor_neutralr : RightIdentity lor lfalse.
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

  Global Instance lattice_hprop : Lattice hProp.
  Proof. repeat (split ; try apply _). Defined.

  Global Instance bounded_jsl_hprop : BoundedJoinSemiLattice hProp.
  Proof. repeat (split ; try apply _). Qed.

  Global Instance top_hprop : Top hProp := Unit_hp.
  Global Instance bounded_msl_hprop : @BoundedSemiLattice hProp (⊓) ⊤.
  Proof.
    repeat (split; try apply _); cbv.
    - intros X. apply path_trunctype ; apply prod_unit_l.
    - intros X. apply path_trunctype ; apply prod_unit_r.
  Defined.
End hPropLattice.
