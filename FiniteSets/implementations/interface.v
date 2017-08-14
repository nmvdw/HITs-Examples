Require Import HoTT.
Require Import FSets.

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
End interface.

Section properties.
  Context `{Univalence}.
  Variable (T : Type -> Type) (f : forall A, T A -> FSet A).
  Context `{sets T f}.

  Definition set_eq : forall A, T A -> T A -> hProp :=
    fun A X Y => (BuildhProp (f A X = f A Y)).

  Definition set_subset : forall A, T A -> T A -> hProp :=
    fun A X Y => (f A X) ⊆ (f A Y).

  Ltac reduce :=
    intros ;
    repeat (rewrite (f_empty T _)
         || rewrite (f_singleton T _)
         || rewrite (f_union T _)
         || rewrite (f_filter T _)
         || rewrite (f_member T _)).

  Definition empty_isIn : forall (A : Type) (a : A),
    a ∈ ∅ = False_hp.
  Proof.
    by reduce.
  Defined.

  Definition singleton_isIn : forall (A : Type) (a b : A),
    a ∈ {|b|} = merely (a = b).
  Proof.
    by reduce.
  Defined.

  Definition union_isIn : forall (A : Type) (a : A) (X Y : T A),
    a ∈ (X ∪ Y) = lor (a ∈ X) (a ∈ Y).
  Proof.
    by reduce.
  Defined.

  Definition filter_isIn : forall (A : Type) (a : A) (ϕ : A -> Bool) (X : T A),
    member a (filter ϕ X) = if ϕ a then member a X else False_hp.
  Proof.
    reduce.
    apply properties.comprehension_isIn.
  Defined.

  Definition reflect_eq : forall (A : Type) (X Y : T A),
    f A X = f A Y -> set_eq A X Y.
  Proof. done. Defined.

  Definition reflect_subset : forall (A : Type) (X Y : T A),
    subset (f A X) (f A Y) -> set_subset A X Y.
  Proof. done. Defined.

  Hint Unfold set_eq set_subset.

  Ltac simplify := intros ; autounfold in * ; apply reflect_eq ; reduce.

  Definition well_defined_union (A : Type) (X1 X2 Y1 Y2 : T A) :
    set_eq A X1 Y1 -> set_eq A X2 Y2 -> set_eq A (union X1 X2) (union Y1 Y2).
  Proof.
    intros HXY1 HXY2.
    simplify.
    by rewrite HXY1, HXY2.
  Defined.

  Definition well_defined_filter (A : Type) (ϕ : A -> Bool) (X Y : T A) :
    set_eq A X Y -> set_eq A (filter ϕ X) (filter ϕ Y).
  Proof.
    intros HXY.
    simplify.
    by rewrite HXY.
  Defined.

  Ltac reflect_equality := simplify ; eauto with lattice_hints typeclass_instances.

  Lemma union_comm : forall A (X Y : T A),
      set_eq A (X ∪ Y) (Y ∪ X).
  Proof.
    reflect_equality.
  Defined.

  Lemma union_assoc : forall A (X Y Z : T A),
    set_eq A ((X ∪ Y) ∪ Z) (X ∪ (Y ∪ Z)).
  Proof.
    reflect_equality.
  Defined.

  Lemma union_idem : forall A (X : T A),
    set_eq A (X ∪ X) X.
  Proof.
    reflect_equality.
  Defined.

  Lemma union_neutral : forall A (X : T A),
    set_eq A (∅ ∪ X) X.
  Proof.
    reflect_equality.
  Defined.

End properties.

Section quot.
Variable (T : Type -> Type).
Variable (f : forall {A : Type}, T A -> FSet A).
Context `{sets T f}.

Definition R A : relation (T A) := set_eq T f A.
Definition View A : Type := quotient (R A).

Arguments f {_} _.

Instance R_refl A : Reflexive (R A).
Proof. intro. reflexivity. Defined.

Instance R_sym A : Symmetric (R A).
Proof. intros a b Hab. apply (Hab^). Defined.

Instance R_trans A: Transitive (R A).
Proof. intros a b c Hab Hbc. apply (Hab @ Hbc). Defined.

(* Instance quotient_recursion `{A : Type} (Q : relation A) `{is_mere_relation _ Q} : HitRecursion (quotient Q) := *)
(*   { *)
(*     indTy := _; recTy := _;  *)
(*     H_inductor := quotient_ind Q; H_recursor := quotient_rec Q *)
(*   }. *)

Instance View_recursion A : HitRecursion (View A) :=
  {
    indTy := _; recTy := forall (P : Type) (HP: IsHSet P) (u : T A -> P), (forall x y : T A, set_eq T (@f) A x y -> u x = u y) -> View A -> P;
    H_inductor := quotient_ind (R A); H_recursor := @quotient_rec _ (R A) _
  }.

Arguments set_eq {_} _ {_} _ _.

Definition View_rec2 {A} (P : Type) (HP : IsHSet P) (u : T A -> T A -> P) :
  (forall (x x' : T A), set_eq (@f) x x' -> forall (y y' : T A), set_eq (@f) y y' -> u x y = u x' y') ->
  forall (x y : View A), P.
Proof.
intros Hresp.
assert (resp1 : forall x y y', set_eq (@f) y y' -> u x y = u x y').
{ intros x y y'.
  apply Hresp.
  reflexivity. }
assert (resp2 : forall x x' y, set_eq (@f) x x' -> u x y = u x' y).
{ intros x x' y Hxx'.
  apply Hresp. apply Hxx'.
  reflexivity. }
hrecursion.
- intros a.
  hrecursion.
  + intros b.
    apply (u a b).
  + intros b b' Hbb'. simpl.
    by apply resp1.
- intros a a' Haa'. simpl.
  apply path_forall. red.
  hinduction.
  + intros b. apply resp2. apply Haa'.
  + intros; apply HP.
Defined.

Instance View_max A : maximum (View A).
Proof.
compute-[View].
simple refine (View_rec2 _ _ _ _).
- intros a b. apply class_of. apply (union a b).
- intros x x' Hxx' y y' Hyy'. simpl.
  apply related_classes_eq.
  unfold R in *.
  eapply well_defined_union; eauto.
Defined.

Ltac reduce :=
  intros ;
  repeat (rewrite (f_empty T _)
          || rewrite (f_singleton T _)
          || rewrite (f_union T _)
          || rewrite (f_filter T _)
          || rewrite (f_member T _)).

Instance View_member A: hasMembership (View A) A.
Proof.
  intros a.
  hrecursion.
  - apply (member a).
  - intros X Y HXY.
    reduce.
    unfold R, set_eq in HXY. rewrite HXY.
    reflexivity.
Defined.

Instance View_empty A: hasEmpty (View A).
Proof.
  apply class_of.
  apply ∅.
Defined.

Instance View_singleton A: hasSingleton (View A) A.
Proof.
  intros a.
  apply class_of.
  apply {|a|}.
Defined.

Instance View_union A: hasUnion (View A).
Proof.
  intros X Y.
  apply (max_L X Y).
Defined.

Instance View_comprehension A: hasComprehension (View A) A.
Proof.
  intros ϕ.
  hrecursion.
  - intros X.
    apply class_of.
    apply (filter ϕ X).
  - intros X X' HXX'. simpl.
    apply related_classes_eq.
    eapply well_defined_filter; eauto.
Defined.

Instance View_max_comm A: Commutative (@max_L (View A) _).
Proof.
  unfold Commutative.
  hinduction.
  - intros X.
    hinduction.
    + intros Y. cbn.
      apply related_classes_eq.
      eapply union_comm; eauto.
    + intros. apply set_path2.
  - intros. apply path_forall; intro. apply set_path2.
Defined.

Ltac buggeroff := intros; apply path_ishprop.

Instance View_max_assoc A: Associative (@max_L (View A) _).
Proof.
  unfold Associative.
  hinduction; try buggeroff.
  intros X.
  hinduction; try buggeroff.
  intros Y.
  hinduction; try buggeroff.
  intros Z. cbn.
  apply related_classes_eq.
  eapply union_assoc; eauto.
Defined.

Instance View_max_idem A: Idempotent (@max_L (View A) _).
Proof.
  unfold Idempotent.
  hinduction; try buggeroff.
  intros X; cbn.
  apply related_classes_eq.
  eapply union_idem; eauto.
Defined.

Instance View_max_neut A: NeutralL (@max_L (View A) _) ∅.
Proof.
  unfold NeutralL.
  hinduction; try buggeroff.
  intros X; cbn.
  apply related_classes_eq.
  eapply union_neutral; eauto.
Defined.

Definition View_FSet A : View A -> FSet A.
Proof.
hrecursion.
- apply f.
- done.
Defined.

Instance View_emb A : IsEmbedding (View_FSet A).
Proof.
apply isembedding_isinj_hset.
unfold isinj.
hrecursion; [ | intros; apply path_ishprop ]. intro X.
hrecursion; [ | intros; apply path_ishprop ]. intro Y.
intros. by apply related_classes_eq.
Defined.

Instance View_surj A: IsSurjection (View_FSet A).
Proof.
apply BuildIsSurjection.
intros X. apply tr.
hrecursion X; try (intros; apply path_ishprop).
- exists ∅. simpl. eapply f_empty; eauto.
- intros a. exists {|a|}; simpl. eapply f_singleton; eauto.
- intros X Y [pX HpX] [pY HpY].
  exists (pX ∪ pY); simpl.
  rewrite <- HpX, <- HpY.
  clear HpX HpY.
  hrecursion pY; [ | intros; apply set_path2]. intro tY.
  hrecursion pX; [ | intros; apply set_path2]. intro tX.
  eapply f_union; eauto.
Defined.

Definition view_iso A : View A <~> FSet A.
Proof.
refine (BuildEquiv _ _ (View_FSet A) _).
apply isequiv_surj_emb; apply _.
Defined.

End quot.
