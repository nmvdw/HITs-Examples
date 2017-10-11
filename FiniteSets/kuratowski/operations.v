(** Operations on the [FSet A] for an arbitrary [A] *)
Require Import HoTT HitTactics prelude.
Require Import kuratowski_sets monad_interface extensionality
        list_representation.isomorphism list_representation.list_representation.

Section operations.
  (** Monad operations. *)
  Definition fset_fmap {A B : Type} : (A -> B) -> FSet A -> FSet B.
  Proof.
    intro f.
    hrecursion.
    - exact ∅.
    - apply (fun a => {|f a|}).
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
    - apply (idem o f).
  Defined.

  Global Instance fset_pure : hasPure FSet.
  Proof.
    split.
    apply (fun _ a => {|a|}).
  Defined.  

  Global Instance fset_bind : hasBind FSet.
  Proof.
    split.
    intros A.
    hrecursion.
    - exact ∅.
    - exact idmap.
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
    - apply union_idem.
  Defined.

  (** Set-theoretical operations. *)
  Global Instance fset_comprehension : forall A, hasComprehension (FSet A) A.
  Proof.
    intros A P.
    hrecursion.
    - apply ∅.
    - intro a.
      refine (if (P a) then {|a|} else ∅).
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
    - intros; simpl.
      apply union_idem.
  Defined.
        
  Definition single_product {A B : Type} (a : A) : FSet B -> FSet (A * B).
  Proof.
    hrecursion.
    - apply ∅.
    - intro b.
      apply {|(a, b)|}.
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
    - intros.
      apply idem.
  Defined.

  Definition product {A B : Type} : FSet A -> FSet B -> FSet (A * B).
  Proof.
    intros X Y.
    hrecursion X.
    - apply ∅.
    - intro a.
      apply (single_product a Y).
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
    - intros ; apply union_idem.
  Defined.

  Definition disjoint_sum {A B : Type} (X : FSet A) (Y : FSet B) : FSet (A + B) :=
    (fset_fmap inl X) ∪ (fset_fmap inr Y).      

  Local Ltac remove_transport
    := intros ; apply path_forall ; intro Z ; rewrite transport_arrow
       ; rewrite transport_const ; simpl.
  Local Ltac pointwise
    := repeat (f_ap) ; try (apply path_forall ; intro Z2) ;
      rewrite transport_arrow, transport_const, transport_sigma
      ; f_ap ; hott_simpl ; simple refine (path_sigma _ _ _ _ _)
      ; try (apply transport_const) ; try (apply path_ishprop).

  Context `{Univalence}.

  (** Separation axiom for finite sets. *)
  Definition separation (A B : Type) : forall (X : FSet A) (f : {a | a ∈ X} -> B), FSet B.
  Proof.
    hinduction.
    - intros f.
      apply ∅.
    - intros a f.
      apply {|f (a; tr idpath)|}.
    - intros X1 X2 HX1 HX2 f.
      pose (fX1 := fun Z : {a : A & a ∈ X1} => f (pr1 Z;tr (inl (pr2 Z)))).
      pose (fX2 := fun Z : {a : A & a ∈ X2} => f (pr1 Z;tr (inr (pr2 Z)))).
      specialize (HX1 fX1).
      specialize (HX2 fX2).
      apply (HX1 ∪ HX2).
    - remove_transport.
      rewrite assoc.
      pointwise.
    - remove_transport.
      rewrite comm.
      pointwise.
    - remove_transport.
      rewrite nl.
      pointwise.
    - remove_transport.
      rewrite nr.
      pointwise.
    - remove_transport.
      rewrite <- (idem (Z (x; tr 1%path))).
      pointwise.
  Defined.

  (** [FSet A] has decidable emptiness. *)  
  Definition isEmpty {A : Type} (X : FSet A) : Decidable (X = ∅).
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - apply (inl idpath).
    - intros.
      refine (inr (fun p => _)).
      refine (transport (fun Z : hProp => Z) (ap (fun z => a ∈ z) p) _).
      apply (tr idpath).
    - intros X Y H1 H2.
      destruct H1 as [p1 | p1], H2 as [p2 | p2].
      * left.
        rewrite p1, p2.
        apply nl.
      * right.
        rewrite p1, nl.
        apply p2.
      * right.
        rewrite p2, nr.
        apply p1.
      * right.
        intros p.
        apply p1.
        apply fset_ext.
        intros.
        apply path_iff_hprop ; try contradiction.
        intro H1.
        refine (transport (fun z => a ∈ z) p _).
        apply (tr(inl H1)).
  Defined.  
End operations.

Section operations_decidable.
  Context {A : Type}.
  Context `{MerelyDecidablePaths A}.
  Context `{Univalence}.

  Global Instance isIn_decidable (a : A) : forall (X : FSet A),
      Decidable (a ∈ X).
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - apply _.
    - apply (m_dec_path _).
    - apply _. 
  Defined.

  Global Instance fset_member_bool : hasMembership_decidable (FSet A) A :=
    fun a X =>
      match (dec a ∈ X) with
      | inl _ => true
      | inr _ => false
      end.

  Global Instance subset_decidable : forall (X Y : FSet A), Decidable (X ⊆ Y).
  Proof.
    hinduction ; try (intros ; apply path_ishprop).
    - apply _.
    - apply _. 
    - unfold subset in *.
      apply _.
  Defined.

  Global Instance fset_subset_bool : hasSubset_decidable (FSet A).
  Proof.
    intros X Y.
    apply (if (dec (X ⊆ Y)) then true else false).
  Defined.

  Global Instance fset_intersection : hasIntersection (FSet A)
    := fun X Y => {|X & (fun a => a ∈_d Y)|}.

  Definition difference := fun X Y => {|X & (fun a => negb a ∈_d Y)|}.
End operations_decidable.

Section FSet_cons_rec.
  Context `{A : Type}.
  
  Variable (P : Type)
           (Pset : IsHSet P)
           (Pe : P)
           (Pcons : A -> FSet A -> P -> P)
           (Pdupl : forall X a p, Pcons a ({|a|} ∪ X) (Pcons a X p) = Pcons a X p)
           (Pcomm : forall X a b p, Pcons a ({|b|} ∪ X) (Pcons b X p)
                                           = Pcons b ({|a|} ∪ X) (Pcons a X p)).
  
  Definition FSet_cons_rec (X : FSet A) : P :=
    FSetC_prim_rec A P Pset Pe
                   (fun a Y p => Pcons a (FSetC_to_FSet Y) p)
                   (fun _ _ => Pdupl _ _)
                   (fun _ _ _ => Pcomm _ _ _)
                   (FSet_to_FSetC X).

  Definition FSet_cons_beta_empty : FSet_cons_rec ∅ = Pe := idpath.
  
  Definition FSet_cons_beta_cons (a : A) (X : FSet A)
    : FSet_cons_rec ({|a|} ∪ X) = Pcons a X (FSet_cons_rec X)
    := ap (fun z => Pcons a z _) (repr_iso_id_l _).
End FSet_cons_rec.
