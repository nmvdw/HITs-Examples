Require Import HoTT.
Require Import disjunction lattice.

Section subobjects.
  Variable A : Type.

  Definition Sub := A -> hProp.
End subobjects.

Section blah.
  Variable A : Type.
  Variable C : (A -> hProp) -> hProp.
  Context `{Univalence}.

  Instance blah : Lattice (Sub A).
  Proof.
    unfold Sub.
    apply _.
  Defined.  

  Definition hasUnion := forall X Y, C X -> C Y -> C (max_fun X Y).
  Definition hasIntersection := forall X Y, C X -> C Y -> C (min_fun X Y).
End blah.
