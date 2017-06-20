Require Import HoTT HitTactics.
Require Export definition operations Ext Lattice.

(* Lemmas relating operations to the membership predicate *)
Section operations_isIn.

Context {A : Type} `{DecidablePaths A}.

Lemma ext `{Funext}  : forall (S T : FSet A), (forall a, isIn a S = isIn a T) -> S = T.
Proof.
  apply fset_ext.
Defined.

(* Union and membership *)
Lemma union_isIn (X Y : FSet A) (a : A) :
  isIn a (U X Y) = orb (isIn a X) (isIn a Y).
Proof.
  reflexivity.
Defined.

(* Intersection and membership. We need a bunch of supporting lemmas *)
Lemma intersection_0l: forall X: FSet A, intersection E X = E.
Proof.
hinduction; 
try (intros ; apply set_path2).
- reflexivity.
- intro a.
  reflexivity.
- intros x y P Q.
  cbn.
  rewrite P.
  rewrite Q.
  apply union_idem.
Defined.

Lemma intersection_0r (X : FSet A) : intersection X E = E.
Proof.
  exact idpath.
Defined.

Lemma intersection_La (X : FSet A) (a : A) :
    intersection (L a) X = if isIn a X then L a else E.
Proof.
hinduction X; try (intros ; apply set_path2).
- reflexivity.
- intro b.
  cbn.
  destruct (dec (a = b)) as [p|np].
  * rewrite p.
    destruct (dec (b = b)) as [|nb]; [reflexivity|].
    by contradiction nb.
  * destruct (dec (b = a)); [|reflexivity].
    by contradiction np.
- unfold intersection.
  intros X Y P Q.
  cbn.
  rewrite P.
  rewrite Q.
  destruct (isIn a X) ; destruct (isIn a Y).
  * apply union_idem.
  * apply nr.
  * apply nl. 
  * apply union_idem.
Defined.

Lemma comprehension_or : forall ϕ ψ (x: FSet A),
    comprehension (fun a => orb (ϕ a) (ψ a)) x = U (comprehension ϕ x) 
    (comprehension ψ x).
Proof.
intros ϕ ψ.
hinduction; try (intros; apply set_path2). 
- cbn. apply (union_idem _)^.
- cbn. intros.
  destruct (ϕ a) ; destruct (ψ a) ; symmetry.
  * apply union_idem.
  * apply nr. 
  * apply nl.
  * apply union_idem.
- simpl. intros x y P Q.
  rewrite P.
  rewrite Q.
  rewrite <- assoc.
  rewrite (assoc  (comprehension ψ x)).
  rewrite (comm  (comprehension ψ x) (comprehension ϕ y)).
  rewrite <- assoc.
  rewrite <- assoc.
  reflexivity.
Defined.

Lemma distributive_La (z : FSet A) (a : A) : forall Y : FSet A, 
       intersection (U (L a) z) Y = U (intersection (L a) Y) (intersection z Y).
Proof.
hinduction; try (intros ; apply set_path2) ; cbn.
- symmetry ; apply nl.
- intros b.
  destruct (dec (b = a)) ; cbn.
  * destruct (isIn b z).
    + rewrite union_idem.
      reflexivity.
    + rewrite nr.
      reflexivity.
  * rewrite nl ; reflexivity.
- intros X1 X2 P Q.
  rewrite P. rewrite Q.
  rewrite <- assoc.
  rewrite (comm (comprehension (fun a0 : A => isIn a0 z) X1)).
  rewrite <- assoc.
  rewrite assoc.
  rewrite (comm (comprehension (fun a0 : A => isIn a0 z) X2)).
  reflexivity.
Defined.

Lemma distributive_intersection_U (X1 X2 Y : FSet A) :
    intersection (U X1 X2) Y = U (intersection X1 Y) (intersection X2 Y).
Proof.
hinduction X1; try (intros ; apply set_path2) ; cbn.
- rewrite intersection_0l.
  rewrite nl.
  rewrite nl.
  reflexivity.
- intro a.
  rewrite intersection_La.
  rewrite distributive_La.
  rewrite intersection_La.
  reflexivity.
- intros Z1 Z2 P Q.
  unfold intersection in *. simpl in *.
  apply comprehension_or.
Defined.

Theorem intersection_isIn (X Y: FSet A) (a : A) :
    isIn a (intersection X Y) = andb (isIn a X) (isIn a Y).
Proof.
hinduction X; try (intros ; apply set_path2) ; cbn.
- rewrite intersection_0l.
  reflexivity.
- intro b.
  rewrite intersection_La.
  destruct (dec (a = b)) ; cbn.
  * rewrite p.
    destruct (isIn b Y).
    + cbn.
      destruct (dec (b = b)); [reflexivity|].
      by contradiction n.
    + reflexivity.
  * destruct (isIn b Y).
    + cbn.
      destruct (dec (a = b)); [|reflexivity].
      by contradiction n.
    + reflexivity.
- intros X1 X2 P Q.
  rewrite distributive_intersection_U. simpl.
  rewrite P.
  rewrite Q.
  destruct (isIn a X1) ; destruct (isIn a X2) ; destruct (isIn a Y) ; 
  reflexivity.
Defined.
End operations_isIn.

(* Some suporting tactics *)
Ltac simplify_isIn :=
  repeat (rewrite ?intersection_isIn ;
          rewrite ?union_isIn).
  
Ltac toBool := try (intro) ;
    intros ; apply ext ; intros ; simplify_isIn ; eauto with bool_lattice_hints.

Section SetLattice.

  Context {A : Type}.
  Context {A_deceq : DecidablePaths A}.
  Context `{Funext}.

  Instance fset_union_com : Commutative (@U A).
  Proof. 
    toBool.
  Defined.

  Instance fset_intersection_com : Commutative intersection.
  Proof.
    toBool.
  Defined.

  Instance fset_union_assoc : Associative (@U A).
  Proof.
    toBool.
  Defined.

  Instance fset_intersection_assoc : Associative intersection.
  Proof.
    toBool.
  Defined.

  Instance fset_union_idem : Idempotent (@U A).
  Proof. exact union_idem. Defined.

  Instance fset_intersection_idem : Idempotent intersection.
  Proof.
    toBool.
  Defined.

  Instance fset_union_nl : NeutralL (@U A) (@E A).
  Proof.
    toBool.
  Defined.

  Instance fset_union_nr : NeutralR (@U A) (@E A).
  Proof.
    toBool.
  Defined.

  Instance fset_absorption_intersection_union : Absorption (@U A) intersection.
  Proof.
    toBool.
  Defined.

  Instance fset_absorption_union_intersection : Absorption intersection (@U A).
  Proof.
    toBool.
  Defined.
  
  Instance lattice_fset : Lattice (@U A) intersection (@E A) :=
    {
      commutative_min := _ ;
      commutative_max := _ ;
      associative_min := _ ;
      associative_max := _ ;
      idempotent_min := _ ;
      idempotent_max := _ ;
      neutralL_min := _ ;
      neutralR_min := _ ;
      absorption_min_max := _ ;
      absorption_max_min := _
    }.

End SetLattice.

(* Other properties *)
Section properties.

Context {A : Type}.
Context {A_deceq : DecidablePaths A}.

(** isIn properties *)
Lemma singleton_isIn (a b: A) : isIn a  (L b) = true -> a = b.
Proof.
  simpl. 
  destruct (dec (a = b)).
  - intro.
    apply p.
  - intro X. 
    contradiction (false_ne_true X).
Defined.

Lemma empty_isIn (a: A) : isIn a E = false.
Proof. 
  reflexivity.
Defined.

(** comprehension properties *)
Lemma comprehension_false Y : comprehension (fun (_ : A) => false) Y = E.
Proof.
hrecursion Y; try (intros; apply set_path2).
- reflexivity.
- reflexivity.
- intros x y IHa IHb.
  rewrite IHa.
  rewrite IHb.
  apply union_idem.
Defined.

Theorem comprehension_subset : forall ϕ (X : FSet A),
    U (comprehension ϕ X) X = X.
Proof.
intros ϕ.
hrecursion; try (intros ; apply set_path2) ; cbn.
- apply union_idem.
- intro a.
  destruct (ϕ a).
  * apply union_idem.
  * apply nl.
- intros X Y P Q.
  rewrite assoc.
  rewrite <- (assoc (comprehension ϕ X) (comprehension ϕ Y) X).
  rewrite (comm (comprehension ϕ Y) X).
  rewrite assoc.
  rewrite P.
  rewrite <- assoc.
  rewrite Q.
  reflexivity.
Defined.

Theorem comprehension_all : forall (X : FSet A),
    comprehension (fun a => isIn a X) X = X.
Proof.
hinduction; try (intros ; apply set_path2).
- reflexivity.
- intro a.
  destruct (dec (a = a)).
  * reflexivity.
  * contradiction (n idpath).
- intros X1 X2 P Q.
  f_ap; (etransitivity; [ apply comprehension_or |]).
  rewrite P. rewrite (comm X1).
  apply comprehension_subset.

  rewrite Q.
  apply comprehension_subset.
Defined.
  
Theorem distributive_U_int `{Funext} (X1 X2 Y : FSet A) :
    U (intersection X1 X2) Y = intersection (U X1 Y) (U X2 Y).
Proof.
  toBool.
  destruct (a ∈ X1), (a ∈ X2), (a ∈ Y); eauto.
Defined.

End properties.
