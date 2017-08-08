(* Operations on [FSetC A] *)
Require Import HoTT HitTactics.
Require Import representations.cons_repr.

Section operations.
  Global Instance fsetc_union : forall A, hasUnion (FSetC A).
  Proof.
    intros A x y.
    hinduction x.
    - apply y.
    - apply Cns.
    - apply dupl.
    - apply comm.
  Defined.

  Global Instance fsetc_singleton : forall A, hasSingleton (FSetC A) A := fun A a => a;;∅.

End operations.