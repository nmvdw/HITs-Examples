(* Definition of Finite Sets as via cons lists *)
Require Import HoTT HitTactics.
Require Export notation.

Module Export FSetC.
  
  Section FSetC.
    Private Inductive FSetC (A : Type) : Type :=
    | Nil : FSetC A
    | Cns : A ->  FSetC A -> FSetC A.

    Global Instance fset_empty : hasEmpty FSetC := Nil.

    Variable A : Type.
    Arguments Cns {_} _ _.
    Infix ";;" := Cns (at level 8, right associativity).
    
    Axiom dupl : forall (a : A) (x : FSetC A),
        a ;; a ;; x = a ;; x. 

    Axiom comm : forall (a b : A) (x : FSetC A),
        a ;; b ;; x = b ;; a ;; x.

    Axiom trunc : IsHSet (FSetC A).

  End FSetC.

  Arguments Cns {_} _ _.
  Arguments dupl {_} _ _.
  Arguments comm {_} _ _ _.

  Infix ";;" := Cns (at level 8, right associativity).

  Section FSetC_induction.

    Variable A: Type.
    Variable (P : FSetC A -> Type).
    Variable (H :  forall x : FSetC A, IsHSet (P x)).
    Variable (eP : P ∅).
    Variable (cnsP : forall (a:A) (x: FSetC A), P x -> P (a ;; x)).
    Variable (duplP : forall (a: A) (x: FSetC A) (px : P x),
	         dupl a x # cnsP a (a;;x) (cnsP a x px) = cnsP a x px).
    Variable (commP : forall (a b: A) (x: FSetC A) (px: P x),
		 comm a b x # cnsP a (b;;x) (cnsP b x px) = 
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


    Axiom FSetC_ind_beta_dupl : forall (a: A) (x : FSetC A),
        apD FSetC_ind (dupl a x) = 	duplP a x (FSetC_ind x).

    Axiom FSetC_ind_beta_comm : forall (a b: A) (x : FSetC A),
        apD FSetC_ind (comm a b x) = commP a b x (FSetC_ind x).

  End FSetC_induction.

  Section FSetC_recursion.

    Variable A: Type.
    Variable (P: Type).
    Variable (H: IsHSet P).
    Variable (nil : P).
    Variable (cns :  A -> P -> P).
    Variable (duplP : forall (a: A) (x: P), cns a (cns a x) = (cns a x)).
    Variable (commP : forall (a b: A) (x: P), cns a (cns b x) = cns b (cns a x)).

    (* Recursion principle *)
    Definition FSetC_rec : FSetC A -> P.
    Proof.
      simple refine (FSetC_ind _ _ _ _ _  _ _ ); 
        try (intros; simple refine ((transport_const _ _) @ _ ));  cbn.
      - apply nil.
      - apply 	(fun a => fun _ => cns a). 
      - apply duplP.
      - apply commP. 
    Defined.

    Definition FSetC_rec_beta_dupl : forall (a: A) (x : FSetC A),
        ap FSetC_rec (dupl a x) = duplP a (FSetC_rec x).
    Proof.
      intros. 
      eapply (cancelL (transport_const (dupl a x) _)).
      simple refine ((apD_const _ _)^ @ _).
      apply FSetC_ind_beta_dupl.
    Defined.

    Definition FSetC_rec_beta_comm : forall (a b: A) (x : FSetC A),
        ap FSetC_rec (comm a b x) = commP a b (FSetC_rec x).
    Proof.
      intros. 
      eapply (cancelL (transport_const (comm a b x) _)).
      simple refine ((apD_const _ _)^ @ _).
      apply FSetC_ind_beta_comm.
    Defined.

  End FSetC_recursion.


  Instance FSetC_recursion A : HitRecursion (FSetC A) :=
    {
      indTy := _; recTy := _; 
      H_inductor := FSetC_ind A; H_recursor := FSetC_rec A
    }.

End FSetC.

Infix ";;" := Cns (at level 8, right associativity).
