(** Definition of Finite Sets as via lists. *)
Require Import HoTT HitTactics.
Require Export set_names.

Module Export FSetC.

  Section FSetC.
    Private Inductive FSetC (A : Type) : Type :=
    | Nil : FSetC A
    | Cns : A ->  FSetC A -> FSetC A.

    Global Instance fset_empty : forall A,hasEmpty (FSetC A) := Nil.

    Variable A : Type.
    Arguments Cns {_} _ _.
    Infix ";;" := Cns (at level 8, right associativity).

    Axiom dupl : forall (a : A) (x : FSetC A),
        a ;; a ;; x = a ;; x.

    Axiom comm_s : forall (a b : A) (x : FSetC A),
        a ;; b ;; x = b ;; a ;; x.

    Axiom trunc : IsHSet (FSetC A).
  End FSetC.

  Arguments Cns {_} _ _.
  Arguments dupl {_} _ _.
  Arguments comm_s {_} _ _ _.

  Infix ";;" := Cns (at level 8, right associativity).

  Section FSetC_induction.
    Variable (A : Type)
             (P : FSetC A -> Type)
             (H :  forall x : FSetC A, IsHSet (P x))
             (eP : P ∅)
             (cnsP : forall (a:A) (x: FSetC A), P x -> P (a ;; x))
             (duplP : forall (a: A) (x: FSetC A) (px : P x),
	         dupl a x # cnsP a (a;;x) (cnsP a x px) = cnsP a x px)
             (commP : forall (a b: A) (x: FSetC A) (px: P x),
		 comm_s a b x # cnsP a (b;;x) (cnsP b x px) =
		 cnsP b (a;;x) (cnsP a x px)).

    (* Induction principle *)
    Fixpoint FSetC_ind
             (x : FSetC A)
             {struct x}
      : P x
      := (match x return _ -> _ -> _ -> P x with
          | Nil => fun _ => fun _ => fun _  => eP
          | a ;; y => fun _ => fun _ => fun _ => cnsP a y (FSetC_ind y)
          end) H duplP commP.
  End FSetC_induction.

  Section FSetC_recursion.
    Variable (A : Type)
             (P : Type)
             (H : IsHSet P)
             (nil : P)
             (cns :  A -> P -> P)
             (duplP : forall (a: A) (x: P), cns a (cns a x) = (cns a x))
             (commP : forall (a b: A) (x: P), cns a (cns b x) = cns b (cns a x)).

    (* Recursion principle *)
    Definition FSetC_rec : FSetC A -> P.
    Proof.
      simple refine (FSetC_ind _ _ _ _ _  _ _ );
        try (intros; simple refine ((transport_const _ _) @ _ ));  cbn.
      - apply nil.
      - apply (fun a => fun _ => cns a).
      - apply duplP.
      - apply commP.
    Defined.
  End FSetC_recursion.

  Instance FSetC_recursion A : HitRecursion (FSetC A) :=
    {
      indTy := _; recTy := _;
      H_inductor := FSetC_ind A; H_recursor := FSetC_rec A
    }.

  Section FSetC_prim_recursion.
    Variable (A : Type)
             (P : Type)
             (H : IsHSet P)
             (nil : P)
             (cns :  A -> FSetC A -> P -> P)
             (duplP : forall (a : A) (X : FSetC A) (x : P),
                 cns a (a ;; X) (cns a X x) = (cns a X x))
             (commP : forall (a b: A) (X : FSetC A) (x: P),
                 cns a (b ;; X) (cns b X x) = cns b (a ;; X) (cns a X x)).

    (* Recursion principle *)
    Definition FSetC_prim_rec : FSetC A -> P.
    Proof.
      simple refine (FSetC_ind A (fun _ => P) (fun _ => H) nil cns _ _ );
        try (intros; simple refine ((transport_const _ _) @ _ ));  cbn.
      - apply duplP.
      - apply commP.
    Defined.
  End FSetC_prim_recursion.
End FSetC.

Infix ";;" := Cns (at level 8, right associativity).
