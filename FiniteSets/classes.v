Require Import HoTT.
From HoTTClasses Require Import interfaces.abstract_algebra tactics.ring_tac.

Section hProp_lattice.
Context `{Univalence}.
  
Definition lor (X Y : hProp) : hProp := BuildhProp (Trunc (-1) (sum X Y)).
Definition land (P Q : hProp) := BuildhProp (prod P Q).
Global Instance join_hprop : Join hProp := lor.
Global Instance meet_hprop : Meet hProp := land.
Global Instance land_associative : Associative land.
Proof.
  intros P Q R.
  apply path_hprop.
  apply equiv_prod_assoc.
Defined.
Global Instance lor_associative : Associative lor.
Proof. 
  intros P Q R. symmetry.
  apply path_iff_hprop ; cbn.
  * simple refine (Trunc_ind _ _).
    intros [xy | z] ; cbn.
  + simple refine (Trunc_ind _ _ xy).
    intros [x | y].
    ++ apply (tr (inl x)). 
    ++ apply (tr (inr (tr (inl y)))).
  + apply (tr (inr (tr (inr z)))).
    * simple refine (Trunc_ind _ _).    
      intros [x | yz] ; cbn.
  + apply (tr (inl (tr (inl x)))).
  + simple refine (Trunc_ind _ _ yz).
    intros [y | z].
    ++ apply (tr (inl (tr (inr y)))). 
    ++ apply (tr (inr z)).
Defined.

Global Instance land_commutative : Commutative land.
Proof. 
  intros P Q.
  apply path_hprop.
  apply equiv_prod_symm.
Defined.

Global Instance lor_commutative : Commutative lor.
Proof. 
  intros P Q. symmetry.
  apply path_iff_hprop ; cbn.
  * simple refine (Trunc_ind _ _).
    intros [x | y].
  + apply (tr (inr x)).
  + apply (tr (inl y)).
    * simple refine (Trunc_ind _ _).
      intros [y | x].
  + apply (tr (inr y)).
  + apply (tr (inl x)).
Defined.

Global Instance joinsemilattice_hprop : JoinSemiLattice hProp.
Proof.
  split.
  - split; [ split | ]; apply _.
  - compute-[lor]. intros P.
    apply path_iff_hprop ; cbn.
    + simple refine (Trunc_ind _ _).
      intros [x | x] ; apply x.
    + apply (fun x => tr (inl x)).
Defined.

Global Instance meetsemilattice_hprop : MeetSemiLattice hProp.
Proof.
  split.
  - split; [ split | ]; apply _.
  - compute-[land]. intros x.
    apply path_iff_hprop ; cbn.
    + intros [a b] ; apply a.
    + intros a ; apply (pair a a).
Defined.

Global Instance lor_land_absorbtion : Absorption join meet.
Proof.
intros P Q.
apply path_iff_hprop ; cbn.
- intros X ; strip_truncations.
  destruct X as [Xx | [Xy1 Xy2]] ; assumption.
- intros X.
  apply (tr (inl X)).
Defined.

Global Instance land_lor_absorbtion : Absorption meet join.
Proof.
intros P Q.
apply path_iff_hprop ; cbn.
- intros [X Y] ; strip_truncations.
  assumption.
- intros X.
  split.
  * assumption.
  * apply (tr (inl X)).
Defined.

Global Instance hprop_lattice : Lattice hProp.
Proof. split; apply _. Defined.

End hProp_lattice.

(* Section lattice_semiring. *)
(*   Context `{A : Type}. *)
(*   Context `{Lattice A}. *)
(*   Context `{Bottom A}. *)
(*   Instance join_plus : Plus A := join. *)
(*   Instance meet_plus : Mult A := meet. *)
(*   Instance bot_zero  : Zero A := bottom. *)

(* End lattice_semiring. *)

Create HintDb lattice_hints.
Hint Resolve associativity : lattice_hints.
Hint Resolve commutativity : lattice_hints.
Hint Resolve absorption : lattice_hints.
Hint Resolve idempotency : lattice_hints.
  
Section fun_lattice.
  Context {A B : Type}.
  Context `{Univalence}.
  Context `{Lattice B}.

  Definition max_fun (f g : (A -> B)) (a : A) : B
    := f a ⊔ g a.

  Definition min_fun (f g : (A -> B)) (a : A) : B
    := f a ⊓ g a.

  Global Instance fun_join : Join (A -> B) := max_fun.
  Global Instance fun_meet : Meet (A -> B) := min_fun.

  Ltac solve_fun :=
    compute ; intros ; apply path_forall ; intro ;
    eauto 10 with lattice_hints typeclass_instances.
  
  Global Instance fun_lattice : Lattice (A -> B).
  Proof.
    repeat (split; try (apply _ || solve_fun)).
  Defined.
End fun_lattice.

Section sub_lattice.
  Context {A : Type} {P : A -> hProp}.
  Context `{Lattice A}.
  Context {Hmax : forall x y, P x -> P y -> P (join x y)}.
  Context {Hmin : forall x y, P x -> P y -> P (meet x y)}.

  Definition AP : Type := sig P.

  Instance join_sub : Join AP := fun (x y : AP) =>
    match x, y with
    | (a ; pa), (b ; pb) =>
      (join a b ; Hmax a b pa pb)
    end.

  Instance meet_sub : Meet AP := fun (x y : AP) =>
    match x, y with
    | (a ; pa), (b ; pb) => 
      (meet a b ; Hmin a b pa pb)      
    end.

  Local Instance hprop_sub : forall c, IsHProp (P c).
  Proof.
    apply _.
  Defined.

  Ltac solve_sub :=
    repeat (intros [? ?]) 
    ; simple refine (path_sigma _ _ _ _ _); [ | apply hprop_sub ]
    ; compute
    ; eauto 10 with lattice_hints typeclass_instances.

  Global Instance sub_lattice : Lattice AP.
  Proof.
    repeat (split; try (apply _ || solve_sub)).
  Defined.

End sub_lattice.
