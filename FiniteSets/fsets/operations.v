(* Operations on the [FSet A] for an arbitrary [A] *)
Require Import HoTT HitTactics.
Require Import representations.definition disjunction lattice.

Section operations.
Context {A : Type}.
Context `{Univalence}.

Definition isIn : A -> FSet A -> hProp.
Proof.
intros a.
hrecursion.
- exists Empty.
  exact _.
- intro a'.
  exists (Trunc (-1) (a = a')).
  exact _.
- apply lor.
- intros ; symmetry ; apply lor_assoc.
- intros ; apply lor_comm.
- intros ; apply lor_nl.
- intros ; apply lor_nr.
- intros ; apply lor_idem.
Defined.

Definition subset : FSet A -> FSet A -> hProp.
Proof.
intros X Y.
hrecursion X.
- exists Unit.
  exact _.
- intros a.
  apply (isIn a Y).
- intros X1 X2.
  exists (prod X1 X2).
  exact _.
- intros.
  apply path_trunctype ; apply equiv_prod_assoc.
- intros.
  apply path_trunctype ; apply equiv_prod_symm.
- intros.
  apply path_trunctype ; apply prod_unit_l.
- intros.
  apply path_trunctype ; apply prod_unit_r.
- intros a'.
  apply path_iff_hprop ; cbn.
  * intros [p1 p2]. apply p1.
  * intros p.
    split ; apply p.
Defined.

Definition comprehension : 
  (A -> Bool) -> FSet A -> FSet A.
Proof.
intros P.
hrecursion.
- apply E.
- intro a.
  refine (if (P a) then L a else E).
- apply U.
- apply assoc.
- apply comm.
- apply nl.
- apply nr.
- intros; simpl. 
  destruct (P x).
  + apply idem.
  + apply nl.
Defined.

Definition isEmpty :
  FSet A -> Bool.
Proof.
  hrecursion.
  - apply true.
  - apply (fun _ => false).
  - apply andb.
  - intros. symmetry. eauto with bool_lattice_hints.
  - eauto with bool_lattice_hints.
  - eauto with bool_lattice_hints.
  - eauto with bool_lattice_hints.
  - eauto with bool_lattice_hints.
Defined.    
  
End operations.

Infix "∈" := isIn (at level 9, right associativity).
Infix  "⊆" := subset (at level 10, right associativity).