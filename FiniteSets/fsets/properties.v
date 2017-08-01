Require Import HoTT HitTactics.
Require Export representations.definition disjunction fsets.operations.

(* Lemmas relating operations to the membership predicate *)
Section operations_isIn.

Context {A : Type}.
Context `{Univalence}.



Lemma union_idem : forall x: FSet A, U x x = x.
Proof.
hinduction; 
try (intros ; apply set_path2) ; cbn.
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

(** ** Properties about subset relation. *)
Lemma subset_union (X Y : FSet A) : 
  subset X Y -> U X Y = Y.
Proof.
hinduction X; try (intros; apply path_forall; intro; apply set_path2).
- intros. apply nl.
- intros a. hinduction Y;
  try (intros; apply path_forall; intro; apply set_path2).
  + intro.
    contradiction.
  + intro a0.
    simple refine (Trunc_ind _ _).
    intro p ; cbn. 
    rewrite p; apply idem.
  + intros X1 X2 IH1 IH2.
    simple refine (Trunc_ind _ _).
    intros [e1 | e2].
    ++ rewrite assoc.
       rewrite (IH1 e1).
       reflexivity.
    ++ rewrite comm.
       rewrite <- assoc.
       rewrite (comm X2).
       rewrite (IH2 e2).
       reflexivity.
- intros X1 X2 IH1 IH2 [G1 G2].
  rewrite <- assoc.
  rewrite (IH2 G2).
  apply (IH1 G1).
Defined.

Lemma subset_union_l (X : FSet A) :
  forall Y, subset X (U X Y).
Proof.
hinduction X ;
  try (repeat (intro; intros; apply path_forall); intro; apply equiv_hprop_allpath ; apply _).
- apply (fun _ => tt).
- intros a Y.
  apply tr ; left ; apply tr ; reflexivity.
- intros X1 X2 HX1 HX2 Y.
  split. 
  * rewrite <- assoc. apply HX1.
  * rewrite (comm X1 X2). rewrite <- assoc. apply HX2.
Defined.

(* Union and membership *)
Lemma union_isIn (X Y : FSet A) (a : A) :
  isIn a (U X Y) = isIn a X ∨ isIn a Y.
Proof.
  reflexivity.
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

End operations_isIn.

(* Other properties *)
Section properties.

Context {A : Type}.
Context `{Univalence}.

(** isIn properties *)
Lemma singleton_isIn (a b: A) : isIn a (L b) -> Trunc (-1) (a = b).
Proof.
  apply idmap.
Defined.

Lemma empty_isIn (a: A) : isIn a E -> Empty.
Proof. 
  apply idmap.
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

Lemma comprehension_subset : forall ϕ (X : FSet A),
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

End properties.
