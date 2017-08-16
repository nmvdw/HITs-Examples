(* [FSet] is a (strong and stable) finite powerset monad *)
Require Import HoTT HitTactics.
Require Export representations.definition fsets.properties fsets.operations.

Definition ffmap {A B : Type} : (A -> B) -> FSet A -> FSet B.
Proof.
  intro f.
  hrecursion.
  - exact ∅.
  - intro a. exact {| f a |}.
  - intros X Y. apply (X ∪ Y).
  - apply assoc.
  - apply comm.
  - apply nl.
  - apply nr.
  - simpl. intro x. apply idem.
Defined.

Lemma ffmap_1 `{Funext} {A : Type} : @ffmap A A idmap = idmap.
Proof.
  apply path_forall.
  intro x. hinduction x; try (intros; f_ap);
             try (intros; apply set_path2).
Defined.

Global Instance fset_functorish `{Funext}: Functorish FSet
  := { fmap := @ffmap; fmap_idmap := @ffmap_1 _ }.

Lemma ffmap_compose {A B C : Type} `{Funext} (f : A -> B) (g : B -> C) :
  fmap FSet (g o f) = fmap _ g o fmap _ f.
Proof.
  apply path_forall. intro x.
  hrecursion x; try (intros; f_ap);
    try (intros; apply set_path2).
Defined.

Definition join {A : Type} : FSet (FSet A) -> FSet A.
Proof.
hrecursion.
- exact ∅.
- exact idmap.
- intros X Y. apply (X ∪ Y).
- apply assoc.
- apply comm.
- apply nl.
- apply nr.
- simpl. apply union_idem.
Defined.

Lemma join_assoc {A : Type} (X : FSet (FSet (FSet A))) :
  join (ffmap join X) = join (join X).
Proof.
  hrecursion X; try (intros; f_ap);
    try (intros; apply set_path2).
Defined.

Lemma join_return_1 {A : Type} (X : FSet A) :
  join ({| X |}) = X.
Proof. reflexivity. Defined.

Lemma join_return_fmap {A : Type} (X : FSet A) :
  join ({| X |}) = join (ffmap (fun x => {|x|}) X).
Proof.
  hrecursion X; try (intros; f_ap);
    try (intros; apply set_path2).
Defined.

Lemma join_fmap_return_1 {A : Type} (X : FSet A) :
  join (ffmap (fun x => {|x|}) X) = X.
Proof. refine ((join_return_fmap _)^ @ join_return_1 _). Defined.

Lemma fmap_isIn `{Univalence} {A B : Type} (f : A -> B) (a : A) (X : FSet A) :
  a ∈ X -> (f a) ∈ (ffmap f X).
Proof.
  hinduction X; try (intros; apply path_ishprop).
  - apply idmap.
  - intros b Hab; strip_truncations.
    apply (tr (ap f Hab)).
  - intros X0 X1 HX0 HX1 Ha.
    strip_truncations. apply tr.
    destruct Ha as [Ha | Ha].
    + left. by apply HX0.
    + right. by apply HX1.
Defined.
