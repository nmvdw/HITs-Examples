(** Interface for lattices and join semilattices. *)
Require Import HoTT.
From HoTT.Classes.interfaces Require Export abstract_algebra canonical_names.
From HoTT.Classes Require Export theory.lattices.

(* (** Join semilattices as a typeclass. They only have a join operator. *) *)
(* Section JoinSemiLattice. *)
(*   Variable A : Type. *)
(*   Context {max_L : Join A} {empty_L : Bottom A}. *)

(*   Class JoinSemiLattice := *)
(*     { *)
(*       commutative_max_js :> Commutative max_L ; *)
(*       associative_max_js :> Associative max_L ; *)
(*       idempotent_max_js :> BinaryIdempotent max_L ; *)
(*       neutralL_max_js :> LeftIdentity max_L empty_L ; *)
(*       neutralR_max_js :> RightIdentity max_L empty_L ; *)
(*     }. *)
(* End JoinSemiLattice. *)

(* Arguments JoinSemiLattice _ {_} {_}. *)

(* Create HintDb joinsemilattice_hints. *)
(* Hint Resolve associativity : joinsemilattice_hints. *)
(* Hint Resolve (associativity _ _ _)^ : joinsemilattice_hints. *)
(* Hint Resolve commutativity : joinsemilattice_hints. *)
(* Hint Resolve idempotency : joinsemilattice_hints. *)
(* Hint Resolve neutralityL : joinsemilattice_hints. *)
(* Hint Resolve neutralityR : joinsemilattice_hints. *)

(* (** Lattices as a typeclass which have both a join and a meet. *) *)
(* Section Lattice. *)
(*   Variable A : Type. *)
(*   Context {max_L : maximum A} {min_L : minimum A} {empty_L : bottom A}. *)

(*   Class Lattice := *)
(*     { *)
(*       commutative_min :> Commutative min_L ; *)
(*       commutative_max :> Commutative max_L ; *)
(*       associative_min :> Associative min_L ; *)
(*       associative_max :> Associative max_L ; *)
(*       idempotent_min :> Idempotent min_L ; *)
(*       idempotent_max :> Idempotent max_L ; *)
(*       neutralL_max :> NeutralL max_L empty_L ; *)
(*       neutralR_max :> NeutralR max_L empty_L ; *)
(*       absorption_min_max :> Absorption min_L max_L ; *)
(*       absorption_max_min :> Absorption max_L min_L *)
(*     }. *)
(* End Lattice. *)

(* Arguments Lattice _ {_} {_} {_}. *)

Create HintDb lattice_hints.
Hint Resolve associativity : lattice_hints.
(* Hint Resolve (associativity _ _ _)^ : lattice_hints. *)
Hint Resolve commutativity : lattice_hints.
Hint Resolve absorption : lattice_hints.
Hint Resolve idempotency : lattice_hints.
Hint Resolve left_identity : lattice_hints.
Hint Resolve right_identity : lattice_hints.
