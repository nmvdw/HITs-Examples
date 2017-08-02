(* Operations on [FSetC A] *)
Require Import HoTT HitTactics.
Require Import representations.cons_repr.

Section operations.

  Context {A : Type}.

  Definition append  (x y: FSetC A) : FSetC A.
    hinduction x.
    - apply y.
    - apply Cns.
    - apply dupl.
    - apply comm.
  Defined.

  Definition singleton (a:A) : FSetC A := a;;∅.

End operations.