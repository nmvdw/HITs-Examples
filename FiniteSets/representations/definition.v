(* Definitions of the Kuratowski-finite sets via a HIT *)
Require Import HoTT HitTactics.
Require Export notation.

Module Export FSet.
  Section FSet.
    Private Inductive FSet (A : Type) : Type :=
    | E : FSet A
    | L : A -> FSet A
    | U : FSet A -> FSet A -> FSet A.

    Global Instance fset_empty : hasEmpty FSet := E.
    Global Instance fset_singleton : hasSingleton FSet := L.
    Global Instance fset_union : hasUnion FSet := U.

    Variable A : Type.
    
    Axiom assoc : forall (x y z : FSet A),
        x ∪ (y ∪ z) = (x ∪ y) ∪ z.

    Axiom comm : forall (x y : FSet A),
        x ∪ y = y ∪ x.

    Axiom nl : forall (x : FSet A),
        ∅ ∪ x = x.

    Axiom nr : forall (x : FSet A),
        x ∪ ∅ = x.

    Axiom idem : forall (x : A),
        {|x|} ∪ {|x|} = {|x|}.

    Axiom trunc : IsHSet (FSet A).

  End FSet.

  Arguments assoc {_} _ _ _.
  Arguments comm {_} _ _.
  Arguments nl {_} _.
  Arguments nr {_} _.
  Arguments idem {_} _.  

  Section FSet_induction.
    Variable A: Type.
    Variable  (P : FSet A -> Type).
    Variable  (H :  forall X : FSet A, IsHSet (P X)).
    Variable  (eP : P ∅).
    Variable  (lP : forall a: A, P {|a|}).
    Variable  (uP : forall (x y: FSet A), P x -> P y -> P (x ∪ y)).
    Variable  (assocP : forall (x y z : FSet A) 
                               (px: P x) (py: P y) (pz: P z),
                  assoc x y z #
                        (uP x (y ∪ z) px (uP y z py pz)) 
                  = 
                  (uP (x ∪ y) z (uP x y px py) pz)).
    Variable  (commP : forall (x y: FSet A) (px: P x) (py: P y),
                  comm x y #
                       uP x y px py = uP y x py px).
    Variable  (nlP : forall (x : FSet A) (px: P x), 
                  nl x # uP ∅ x eP px = px).
    Variable  (nrP : forall (x : FSet A) (px: P x), 
                  nr x # uP x ∅ px eP = px).
    Variable  (idemP : forall (x : A), 
                  idem x # uP {|x|} {|x|} (lP x) (lP x) = lP x).
    
    (* Induction principle *)
    Fixpoint FSet_ind
             (x : FSet A)
             {struct x}
      : P x
      := (match x return _ -> _ -> _ -> _ -> _ -> _ -> P x with
          | E => fun _ _ _ _ _ _ => eP
          | L a => fun _ _ _ _ _ _ => lP a
          | U y z => fun _ _ _ _ _ _ => uP y z (FSet_ind y) (FSet_ind z)
          end) H assocP commP nlP nrP idemP.

    Axiom FSet_ind_beta_assoc : forall (x y z : FSet A),
        apD FSet_ind (assoc x y z) =
        (assocP x y z (FSet_ind x)  (FSet_ind y) (FSet_ind z)).

    Axiom FSet_ind_beta_comm : forall (x y : FSet A),
        apD FSet_ind (comm x y) = (commP x y (FSet_ind x) (FSet_ind y)).

    Axiom FSet_ind_beta_nl : forall (x : FSet A),
        apD FSet_ind (nl x) = (nlP x (FSet_ind x)).

    Axiom FSet_ind_beta_nr : forall (x : FSet A),
        apD FSet_ind (nr x) = (nrP x (FSet_ind x)).

    Axiom FSet_ind_beta_idem : forall (x : A), apD FSet_ind (idem x) = idemP x.
  End FSet_induction.

  Section FSet_recursion.

    Variable A : Type.
    Variable P : Type.
    Variable H: IsHSet P.
    Variable e : P.
    Variable l : A -> P.
    Variable u : P -> P -> P.
    Variable assocP : forall (x y z : P), u x (u y z) = u (u x y) z.
    Variable commP : forall (x y : P), u x y = u y x.
    Variable nlP : forall (x : P), u e x = x.
    Variable nrP : forall (x : P), u x e = x.
    Variable idemP : forall (x : A), u (l x) (l x) = l x.

    Definition FSet_rec : FSet A -> P.
    Proof.
      simple refine (FSet_ind A _ _ _ _ _ _ _ _ _ _)
      ; try (intros ; simple refine ((transport_const _ _) @ _)) ; cbn.
      - apply e.
      - apply l.
      - intros x y ; apply u.
      - apply assocP.
      - apply commP.
      - apply nlP.
      - apply nrP.
      - apply idemP.
    Defined.

    Definition FSet_rec_beta_assoc : forall (x y z : FSet A),
        ap FSet_rec (assoc x y z) 
        =
        assocP (FSet_rec x) (FSet_rec y) (FSet_rec z).
    Proof.
      intros.
      unfold FSet_rec.
      eapply (cancelL (transport_const (assoc x y z) _)).
      simple refine ((apD_const _ _)^ @ _).
      apply FSet_ind_beta_assoc.
    Defined.

    Definition FSet_rec_beta_comm : forall (x y : FSet A),
        ap FSet_rec (comm x y) 
        =
        commP (FSet_rec x) (FSet_rec y).
    Proof.
      intros.
      unfold FSet_rec.
      eapply (cancelL (transport_const (comm x y) _)).
      simple refine ((apD_const _ _)^ @ _).
      apply FSet_ind_beta_comm.
    Defined.

    Definition FSet_rec_beta_nl : forall (x : FSet A),
        ap FSet_rec (nl x) 
        =
        nlP (FSet_rec x).
    Proof.
      intros.
      unfold FSet_rec.
      eapply (cancelL (transport_const (nl x) _)).
      simple refine ((apD_const _ _)^ @ _).
      apply FSet_ind_beta_nl.
    Defined.

    Definition FSet_rec_beta_nr : forall (x : FSet A),
        ap FSet_rec (nr x) 
        =
        nrP (FSet_rec x).
    Proof.
      intros.
      unfold FSet_rec.
      eapply (cancelL (transport_const (nr x) _)).
      simple refine ((apD_const _ _)^ @ _).
      apply FSet_ind_beta_nr.
    Defined.

    Definition FSet_rec_beta_idem : forall (a : A),
        ap FSet_rec (idem a) 
        =
        idemP a.
    Proof.
      intros.
      unfold FSet_rec.
      eapply (cancelL (transport_const (idem a) _)).
      simple refine ((apD_const _ _)^ @ _).
      apply FSet_ind_beta_idem.
    Defined.
    
  End FSet_recursion.

  Instance FSet_recursion A : HitRecursion (FSet A) :=
    {
      indTy := _; recTy := _; 
      H_inductor := FSet_ind A; H_recursor := FSet_rec A
    }.

End FSet.

Lemma union_idem {A : Type} : forall x: FSet A, x ∪ x = x.
Proof.
  hinduction ; try (intros ; apply set_path2).
  - apply nl.
  - apply idem.
  - intros x y P Q.
    rewrite assoc.
    rewrite (comm x y).
    rewrite <- (assoc y x x).
    rewrite P.
    rewrite (comm y x).
    rewrite <- (assoc x y y).
    f_ap. 
Defined.