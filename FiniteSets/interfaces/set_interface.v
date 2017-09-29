Require Import HoTT.
Require Import FSets lattice_interface.

Section interface.
  Context `{Univalence}.
  Variable (T : Type -> Type)
           (f : forall A, T A -> FSet A).
  Context `{forall A, hasMembership (T A) A
          , forall A, hasEmpty (T A)
          , forall A, hasSingleton (T A) A
          , forall A, hasUnion (T A)
          , forall A, hasComprehension (T A) A}.

  Class sets :=
    {
      f_empty : forall A, f A ∅ = ∅ ;
      f_singleton : forall A a, f A (singleton a) = {|a|};
      f_union : forall A X Y, f A (union X Y) = (f A X) ∪ (f A Y);
      f_filter : forall A φ X, f A (filter φ X) = {| f A X & φ |};
      f_member : forall A a X, member a X = a ∈ (f A X)
    }.

  Global Instance f_surjective A `{sets} : IsSurjection (f A).
  Proof.
    unfold IsSurjection.
    hinduction ; try (intros ; apply path_ishprop).
    - simple refine (BuildContr _ _ _).
      * refine (tr(∅;_)).
        apply f_empty.
      * intros ; apply path_ishprop.
    - intro a.
      simple refine (BuildContr _ _ _).
      * refine (tr({|a|};_)).
        apply f_singleton.
      * intros ; apply path_ishprop.
    - intros Y1 Y2 [X1' ?] [X2' ?].
      simple refine (BuildContr _ _ _).
      * simple refine (Trunc_rec _ X1') ; intros [X1 fX1].
        simple refine (Trunc_rec _ X2') ; intros [X2 fX2].
        refine (tr(X1 ∪ X2;_)).
        rewrite f_union, fX1, fX2.
        reflexivity.
      * intros ; apply path_ishprop.
  Defined.

End interface.

Section quotient_surjection.
  Variable (A B : Type)
           (f : A -> B)
           (H : IsSurjection f).
  Context `{IsHSet B} `{Univalence}.

  Definition f_eq : relation A := fun a1 a2 => f a1 = f a2.
  Definition quotientB : Type := quotient f_eq.

  Global Instance quotientB_recursion : HitRecursion quotientB :=
    {
      indTy := _;
      recTy :=
        forall (P : Type) (HP: IsHSet P) (u : A -> P),
          (forall x y : A, f_eq x y -> u x = u y) -> quotientB -> P;
      H_inductor := quotient_ind f_eq ;
      H_recursor := @quotient_rec _ f_eq _
    }.

  Global Instance R_refl : Reflexive f_eq.
  Proof.
    intro.
    reflexivity.
  Defined.

  Global Instance R_sym : Symmetric f_eq.
  Proof.
    intros a b Hab.
    apply (Hab^).
  Defined.

  Global Instance R_trans : Transitive f_eq.
  Proof.
    intros a b c Hab Hbc.
    apply (Hab @ Hbc).
  Defined.

  Definition quotientB_to_B : quotientB -> B.
  Proof.
    hrecursion.
    - apply f.
    - done.
  Defined.
    
  Instance quotientB_emb : IsEmbedding (quotientB_to_B).
  Proof.
    apply isembedding_isinj_hset.
    unfold isinj.
    hrecursion ; [ | intros; apply path_ishprop ].
    intro.
    hrecursion ; [ | intros; apply path_ishprop ].
    intros.
      by apply related_classes_eq.
  Defined.

  Instance quotientB_surj : IsSurjection (quotientB_to_B).
  Proof.
    apply BuildIsSurjection.
    intros Y.
    destruct (H Y).
    simple refine (Trunc_rec _ center) ; intros [a fa].
    apply (tr(class_of _ a;fa)).
  Defined.

  Definition quotient_iso : quotientB <~> B.
  Proof.
    refine (BuildEquiv _ _ quotientB_to_B _).
    apply isequiv_surj_emb ; apply _.
  Defined.

  Definition reflect_eq : forall (X Y : A),
      f X = f Y -> f_eq X Y.
  Proof.
    done.
  Defined.

  Lemma same_class : forall (X Y : A),
      class_of f_eq X = class_of f_eq Y -> f_eq X Y.
  Proof.
    intros.
    simple refine (classes_eq_related _ _ _ _) ; assumption.
  Defined.

End quotient_surjection.

Arguments quotient_iso {_} {_} _ {_} {_} {_}.
  
Ltac reduce T :=
  intros ;
  repeat (rewrite (f_empty T _)
          || rewrite (f_singleton T _)
          || rewrite (f_union T _)
          || rewrite (f_filter T _)
          || rewrite (f_member T _)).

Section quotient_properties.
  Variable (T : Type -> Type).
  Variable (f : forall {A : Type}, T A -> FSet A).
  Context `{sets T f}.

  Definition set_eq A := f_eq (T A) (FSet A) (f A).
  Definition View A : Type := quotientB (T A) (FSet A) (f A).

  Instance f_is_surjective A : IsSurjection (f A).
  Proof.
    apply (f_surjective T f A).
  Defined.
    
  Global Instance view_union (A : Type) : hasUnion (View A).
  Proof.
    intros X Y.
    apply (quotient_iso _)^-1.
    simple refine (union _ _).
    - simple refine (quotient_iso (f A) X).
    - simple refine (quotient_iso (f A) Y).
  Defined.

  Definition well_defined_union (A : Type) (X Y : T A) :
    (class_of _ X) ∪ (class_of _ Y) = class_of _ (X ∪ Y).
  Proof.
    rewrite <- (eissect (quotient_iso _)).
    simpl.
    rewrite (f_union T _).
    reflexivity.
  Defined.

  Global Instance view_comprehension (A : Type) : hasComprehension (View A) A.
  Proof.
    intros ϕ X.
    apply (quotient_iso _)^-1.
    simple refine ({|_ & ϕ|}).
    apply (quotient_iso (f A) X).
  Defined.

  Definition well_defined_filter (A : Type) (ϕ : A -> Bool) (X : T A) :
    {|class_of _ X & ϕ|} = class_of _ {|X & ϕ|}.
  Proof.
    rewrite <- (eissect (quotient_iso _)).
    simpl.
    rewrite (f_filter T _).
    reflexivity.
  Defined.

  Global Instance View_empty A : hasEmpty (View A).
  Proof.
    apply ((quotient_iso _)^-1 ∅).
  Defined.

  Definition well_defined_empty A : ∅ = class_of (set_eq A) ∅.
  Proof.
    rewrite <- (eissect (quotient_iso _)).
    simpl.
    rewrite (f_empty T _).
    reflexivity.
  Defined.  

  Global Instance View_singleton A: hasSingleton (View A) A.
  Proof.
    intro a ; apply ((quotient_iso _)^-1 {|a|}).
  Defined.

  Definition well_defined_sungleton A (a : A) : {|a|} = class_of _ {|a|}.
  Proof.
    rewrite <- (eissect (quotient_iso _)).
    simpl.
    rewrite (f_singleton T _).
    reflexivity.
  Defined.  
  
  Global Instance View_member A : hasMembership (View A) A.
  Proof.
    intros a ; unfold View.
    hrecursion.
    - apply (member a).
    - intros X Y HXY.
      reduce T.
      apply (ap _ HXY).
  Defined.

  Instance View_max A : maximum (View A).
  Proof.
    apply view_union.
  Defined.

  Hint Unfold Commutative Associative Idempotent NeutralL NeutralR View_max view_union.

  Instance bottom_view A : bottom (View A).
  Proof.
    apply View_empty.
  Defined.

  Ltac sq1 := autounfold ; intros ; try f_ap
                         ; rewrite ?(eisretr (quotient_iso _))
                         ; eauto with lattice_hints typeclass_instances.

  Ltac sq2 := autounfold ; intros
              ; rewrite <- (eissect (quotient_iso _)), ?(eisretr (quotient_iso _))
              ; f_ap ; simpl
              ; reduce T ; eauto with lattice_hints typeclass_instances.

  Global Instance view_lattice A : JoinSemiLattice (View A).
  Proof.
    split ; try sq1 ; try sq2.
  Defined.

End quotient_properties.

Arguments set_eq {_} _ {_} _ _.

Section properties.
  Variable (T : Type -> Type) (f : forall A, T A -> FSet A).
  Context `{sets T f}.

  Definition set_subset : forall A, T A -> T A -> hProp :=
    fun A X Y => (f A X) ⊆ (f A Y).

  Definition empty_isIn : forall (A : Type) (a : A),
    a ∈ ∅ = False_hp.
  Proof.
    by (reduce T).
  Defined.

  Definition singleton_isIn : forall (A : Type) (a b : A),
    a ∈ {|b|} = merely (a = b).
  Proof.
    by (reduce T).
  Defined.

  Definition union_isIn : forall (A : Type) (a : A) (X Y : T A),
    a ∈ (X ∪ Y) = lor (a ∈ X) (a ∈ Y).
  Proof.
    by (reduce T).
  Defined.

  Definition filter_isIn : forall (A : Type) (a : A) (ϕ : A -> Bool) (X : T A),
    member a (filter ϕ X) = if ϕ a then member a X else False_hp.
  Proof.
    reduce T.
    apply properties.comprehension_isIn.
  Defined.

  Definition reflect_f_eq : forall (A : Type) (X Y : T A),
      class_of (set_eq f) X = class_of (set_eq f) Y -> set_eq f X Y.
  Proof.
    intros.
    refine (same_class _ _ _ _ _ _) ; assumption.
  Defined.

  Global Instance test (A : Type) (X Y : T A)
    : IsHProp  (forall a : A, a ∈ X = a ∈ Y).
  Proof.
    apply _.
  Defined.  

  Lemma f_eq_ext (A : Type) (X Y : T A) :
    (forall a : A, a ∈ X = a ∈ Y) <~> set_eq f X Y.
  Proof.
    eapply equiv_iff_hprop_uncurried ; split.
    - intros HX.
      unfold set_eq, f_eq.
      apply fset_ext.
      intros a.
      rewrite <- ?(f_member T _).
      apply HX.
    - intros HX a.
      rewrite ?(f_member T _).
      f_ap.
  Defined.
    
  Ltac via_quotient := intros ; apply reflect_f_eq ; simpl
                       ; rewrite <- ?(well_defined_union T _), <- ?(well_defined_empty T _)
                       ; eauto with lattice_hints typeclass_instances.  

  Lemma union_comm : forall A (X Y : T A),
      set_eq f (X ∪ Y) (Y ∪ X).
  Proof.
    via_quotient.
  Defined.

  Lemma union_assoc : forall A (X Y Z : T A),
    set_eq f ((X ∪ Y) ∪ Z) (X ∪ (Y ∪ Z)).
  Proof.
    via_quotient.
  Defined.

  Lemma union_idem : forall A (X : T A),
    set_eq f (X ∪ X) X.
  Proof.
    via_quotient.
  Defined.

  Lemma union_neutralL : forall A (X : T A),
    set_eq f (∅ ∪ X) X.
  Proof.
    via_quotient.
  Defined.

  Lemma union_neutralR : forall A (X : T A),
    set_eq f (X ∪ ∅) X.
  Proof.
    via_quotient.
  Defined.
  
End properties.