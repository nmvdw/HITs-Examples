(* Enumerated finite sets *)
Require Import HoTT.
Require Import disjunction.
Require Import representations.cons_repr representations.definition variations.k_finite.
From fsets Require Import operations isomorphism.

Definition Sub A := A -> hProp.

Fixpoint listExt {A} (ls : list A) : Sub A := fun x =>
  match ls with
  | nil => False_hp
  | cons a ls' => BuildhProp (Trunc (-1) (x = a)) ∨ listExt ls' x
  end.

Fixpoint map {A B} (f : A -> B) (ls : list A) : list B :=
  match ls with
  | nil       => nil
  | cons x xs => cons (f x) (map f xs)
  end.

Fixpoint filterD {A} (P : A -> Bool) (ls : list A) : list { x : A | P x = true }.
Proof.
destruct ls as [|x xs].
- exact nil.
- enough ((P x = true) + (P x = false)) as HP.
  { destruct HP as [HP | HP].
    + refine (cons (exist _ x HP) (filterD _ P xs)).
    + refine (filterD _ P xs).
  }
  { destruct (P x); [left | right]; reflexivity. }
Defined.

Lemma filterD_cons {A} (P : A -> Bool) (a : A) (ls : list A) (Pa : P a = true) :
  filterD P (cons a ls) = cons (a;Pa) (filterD P ls).
Proof.
  simpl.
  destruct (if P a as b return ((b = true) + (b = false))
     then inl 1%path
     else inr 1%path) as [Pa' | Pa'].
  - rewrite (set_path2 Pa Pa'). reflexivity.
  - rewrite Pa in Pa'. contradiction (true_ne_false Pa').
Defined.

Lemma filterD_cons_no {A} (P : A -> Bool) (a : A) (ls : list A) (Pa : P a = false) :
  filterD P (cons a ls) = filterD P ls.
Proof.
  simpl.
  destruct (if P a as b return ((b = true) + (b = false))
     then inl 1%path
     else inr 1%path) as [Pa' | Pa'].
  - rewrite Pa' in Pa. contradiction (true_ne_false Pa). 
  - reflexivity.
Defined.

Lemma filterD_lookup {A} (P : A -> Bool) (x : A) (ls : list A) (Px : P x = true) :
  listExt ls x -> listExt (filterD P ls) (x;Px).
Proof.
induction ls as [| a ls].
- simpl. exact idmap.
- assert ((P a = true) + (P a = false)) as HPA.
  { destruct (P a); [left | right]; reflexivity. }
  destruct HPA as [Pa | Pa].
  + rewrite (filterD_cons P a ls Pa). simpl.
    simple refine (Trunc_ind _ _). intros [Hxa | HIH]; apply tr.
    * left. strip_truncations.
      apply tr.
      apply path_sigma' with Hxa.
      apply set_path2.
    * right. apply (IHls HIH).
  + rewrite (filterD_cons_no P a ls Pa). simpl.
    simple refine (Trunc_ind _ _). intros [Hxa | HIH].
    * strip_truncations.
      rewrite <- Hxa in Pa. rewrite Px in Pa.
      contradiction (true_ne_false Pa).
    * apply IHls. apply HIH.
Defined.

(** Definition of finite sets in an enumerated sense *)
Definition enumerated (A : Type) : Type :=
  exists ls, forall (a : A), listExt ls a.

(** Properties of enumerated sets: closed under decidable subsets *)
Lemma enumerated_comprehension (A : Type) (P : A -> Bool) :
  enumerated A -> enumerated { x : A | P x = true }.
Proof.
  intros [eA HeA].
  exists (filterD P eA).
  intros [x Px].
  apply filterD_lookup.
  apply (HeA x).
Defined.

Lemma map_listExt {A B} (f : A -> B) (ls : list A) (y : A) :
  listExt ls y -> listExt (map f ls) (f y).
Proof.
induction ls.
- simpl. apply idmap.
- simpl. simple refine (Trunc_ind _ _). intros [Hxa | HIH]; apply tr.
  + left. strip_truncations. apply tr. f_ap.
  + right. apply IHls. apply HIH.
Defined.

(** Properties of enumerated sets: closed under surjections *)
Lemma enumerated_surj (A B : Type) (f : A -> B) :
  IsSurjection f -> enumerated A -> enumerated B.
Proof.
  intros Hsurj [eA HeA].
  exists (map f eA).
  intros x. specialize (Hsurj x).
  pose (t := center (merely (hfiber f x))).
  simple refine (@Trunc_rec (-1) (hfiber f x) (listExt (map f eA) x) _ _ t).
  intros [y Hfy].
  specialize (HeA y). rewrite <- Hfy.
  apply map_listExt. apply HeA.
Defined.

Lemma listExt_app_r {A} (ls ls' : list A) (x : A) :
  listExt ls x -> listExt (ls ++ ls') x.
Proof.
induction ls; simpl.
- exact Empty_rec.
- simple refine (Trunc_ind _ _). intros [Hxa | HIH]; apply tr.
  + left. apply Hxa.
  + right. apply IHls. apply HIH.
Defined.

Lemma listExt_app_l {A} (ls ls' : list A) (x : A) :
  listExt ls x -> listExt (ls' ++ ls) x.
Proof.
induction ls'; simpl.
- apply idmap.
- intros Hls.
  apply tr.
  right. apply IHls'. apply Hls.
Defined.

(** Properties of enumerated sets: closed under sums *)
Lemma enumerated_sum (A B : Type) :
  enumerated A -> enumerated B -> enumerated (A + B).
Proof.
intros [eA HeA] [eB HeB].
exists (app (map inl eA) (map inr eB)).
intros [x | x].
- apply listExt_app_r. apply map_listExt. apply HeA.
- apply listExt_app_l. apply map_listExt. apply HeB.
Defined.

Fixpoint listProd_sing {A B} (x : A) (ys : list B) : list (A * B).
Proof.
destruct ys as [|y ys].
- exact nil.
- refine (cons (x,y) _).
  apply (listProd_sing _ _ x ys).
Defined.

Fixpoint listProd {A B} (xs : list A) (ys : list B) : list (A * B).
Proof.  
destruct xs as [|x xs].
- exact nil.
- refine (app _ _).
  + exact (listProd_sing x ys).
  + exact (listProd _ _ xs ys).
Defined.

Lemma listExt_prod_sing {A B} (x : A) (y : B) (ys : list B) : 
  listExt ys y -> listExt (listProd_sing x ys) (x, y).
Proof.
induction ys; simpl.
- exact idmap.
- simple refine (Trunc_ind _ _). intros [Hxy | HIH]; simpl; apply tr.
  + left. strip_truncations. apply tr. f_ap.
  + right. apply IHys. apply HIH.
Defined.

Lemma listExt_prod `{Funext} {A B} (xs : list A) (ys : list B) : forall (x : A) (y : B),
  listExt xs x -> listExt ys y -> listExt (listProd xs ys) (x,y).
Proof.
induction xs as [| x' xs]; intros x y.
- simpl. contradiction.
- simpl. simple refine (Trunc_ind _ _). intros Htx. simpl.
  induction ys as [| y' ys].
  + simpl. contradiction.
  + simpl. simple refine (Trunc_ind _ _). intros Hty. simpl. apply tr.
    destruct Htx as [Hxx' | Hxs], Hty as [Hyy' | Hys].
    * left. strip_truncations. apply tr. f_ap.
    * right. strip_truncations. rewrite <- Hxx'. clear Hxx'.
      apply listExt_app_r.
      apply listExt_prod_sing. assumption.
    * right. strip_truncations. rewrite <- Hyy'.
      rewrite <- Hyy' in IHxs.
      apply listExt_app_l. apply IHxs. assumption.
      simpl. apply tr. left. apply tr. reflexivity.
    * right. 
      apply listExt_app_l.
      apply IHxs. assumption.
      simpl. apply tr. right. assumption.
Defined.      

(** Properties of enumerated sets: closed under products *)
Lemma enumerated_prod (A B : Type) `{Funext} :
  enumerated A -> enumerated B -> enumerated (A * B).
Proof.
  intros [eA HeA] [eB HeB].
  exists (listProd eA eB).
  intros [x y].
  apply listExt_prod; [ apply HeA | apply HeB ].
Defined.

(** If a set is enumerated is it Kuratowski-finite *)
Section enumerated_fset.
  Variable A : Type.
  Context `{Univalence}.

  Fixpoint list_to_fset (ls : list A) : FSet A :=
    match ls with
    | nil => ∅
    | cons x xs => {|x|} ∪ (list_to_fset xs)
    end.
  
  Lemma list_to_fset_ext (ls : list A) (a : A):
    listExt ls a -> isIn a (list_to_fset ls).
  Proof.
    induction ls as [|x xs]; simpl.
    - apply idmap.
    - intros Hin.
      strip_truncations. apply tr.
      destruct Hin as [Hax | Hin].
      + left. exact Hax.
      + right. by apply IHxs.
  Defined.

  Lemma enumerated_Kf : enumerated A -> Kf A.
  Proof.
    intros [ls Hls].
    exists (list_to_fset ls). 
    apply path_forall. intro a.
    symmetry. apply path_hprop.
    apply if_hprop_then_equiv_Unit. apply _.
    by apply list_to_fset_ext.
  Defined.
End enumerated_fset.
