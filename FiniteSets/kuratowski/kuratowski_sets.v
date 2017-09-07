(** Definitions of the Kuratowski-finite sets via a HIT *)
Require Import HoTT HitTactics.
Require Export set_names lattice_examples.

Module Export FSet.
  Section FSet.
    Private Inductive FSet (A : Type) : Type :=
    | E : FSet A
    | L : A -> FSet A
    | U : FSet A -> FSet A -> FSet A.

    Global Instance fset_empty : forall A, hasEmpty (FSet A) := E.
    Global Instance fset_singleton : forall A, hasSingleton (FSet A) A := L.
    Global Instance fset_union : forall A, hasUnion (FSet A) := U.

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
    Variable (A : Type)
             (P : FSet A -> Type)
             (H :  forall X : FSet A, IsHSet (P X))
             (eP : P ∅)
             (lP : forall a: A, P {|a|})
             (uP : forall (x y: FSet A), P x -> P y -> P (x ∪ y))
             (assocP : forall (x y z : FSet A)
                               (px: P x) (py: P y) (pz: P z),
                  assoc x y z #
                        (uP x (y ∪ z) px (uP y z py pz))
                  =
                  (uP (x ∪ y) z (uP x y px py) pz))
             (commP : forall (x y: FSet A) (px: P x) (py: P y),
                  comm x y #
                       uP x y px py = uP y x py px)
             (nlP : forall (x : FSet A) (px: P x),
                  nl x # uP ∅ x eP px = px)
             (nrP : forall (x : FSet A) (px: P x),
                  nr x # uP x ∅ px eP = px)
             (idemP : forall (x : A),
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
  End FSet_induction.

  Section FSet_recursion.
    Variable (A : Type)
             (P : Type)
             (H: IsHSet P)
             (e : P)
             (l : A -> P)
             (u : P -> P -> P)
             (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
             (commP : forall (x y : P), u x y = u y x)
             (nlP : forall (x : P), u e x = x)
             (nrP : forall (x : P), u x e = x)
             (idemP : forall (x : A), u (l x) (l x) = l x).

    (* Recursion princople *)
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
    apply (ap (x ∪) Q).
Defined.

Section relations.
  Context `{Univalence}.

  (** Membership of finite sets. *) 
  Global Instance fset_member : forall A, hasMembership (FSet A) A.
  Proof.
    intros A a.
    hrecursion.
    - apply False_hp.
    - apply (fun a' => merely(a = a')).
    - apply lor.
    - eauto with lattice_hints typeclass_instances.
    - eauto with lattice_hints typeclass_instances.
    - eauto with lattice_hints typeclass_instances.
    - eauto with lattice_hints typeclass_instances.
    - eauto with lattice_hints typeclass_instances.
  Defined.

  (** Subset relation of finite sets. *)
  Global Instance fset_subset : forall A, hasSubset (FSet A).
  Proof.
    intros A X Y.
    hrecursion X.
    - apply Unit_hp.
    - apply (fun a => a ∈ Y).
    - intros X1 X2.
      exists (prod X1 X2).
      exact _.
    - eauto with lattice_hints typeclass_instances. 
    - eauto with lattice_hints typeclass_instances.
    - intros.
      apply path_trunctype ; apply prod_unit_l.
    - intros.
      apply path_trunctype ; apply prod_unit_r.
    - eauto with lattice_hints typeclass_instances.
  Defined.
End relations.