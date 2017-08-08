(* Operations on [FSetC A] *)
Require Import HoTT HitTactics.
Require Import representations.cons_repr.

Section operations.

  Global Instance fsetc_union : hasUnion FSetC.
  Proof.
    intros A x y.
    hinduction x.
    - apply y.
    - apply Cns.
    - apply dupl.
    - apply comm.
  Defined.

  Global Instance fsetc_singleton : hasSingleton FSetC := fun A a => a;;∅.

End operations.