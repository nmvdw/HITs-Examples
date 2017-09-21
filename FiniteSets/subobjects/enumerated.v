(* Enumerated finite sets *)
Require Import HoTT HitTactics.
Require Import sub prelude FSets list_representation subobjects.k_finite
        list_representation.isomorphism
        lattice_interface lattice_examples.

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
Definition enumerated (A : Type) : hProp :=
  hexists (fun ls => forall (a : A), listExt ls a).

(** Properties of enumerated sets: closed under decidable subsets *)
Lemma enumerated_comprehension (A : Type) (P : A -> Bool) :
  enumerated A -> enumerated { x : A | P x = true }.
Proof.
  intros HeA. strip_truncations. destruct HeA as [eA HeA].
  apply tr.
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
  intros Hsurj HeA. strip_truncations; apply tr.
  destruct HeA as [eA HeA].
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
  intros HeA HeB.
  strip_truncations; apply tr.
  destruct HeA as [eA HeA], HeB as [eB HeB].
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
  intros HeA HeB.
  strip_truncations; apply tr.
  destruct HeA as [eA HeA], HeB as [eB HeB].
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
    listExt ls a -> a ∈ (list_to_fset ls).
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
    intros Hls.
    strip_truncations.
    destruct Hls as [ls Hls].
    exists (list_to_fset ls).
    apply path_forall. intro a.
    symmetry. apply path_hprop.
    apply if_hprop_then_equiv_Unit. apply _.
    by apply list_to_fset_ext.
  Defined.
End enumerated_fset.

Section fset_dec_enumerated.
  Variable A : Type.
  Context `{Univalence}.

  Definition merely_enumeration_FSet :
    forall (X : FSet A),
    hexists (fun (ls : list A) => forall a, a ∈ X = listExt ls a).
  Proof.
    simple refine (FSet_cons_ind _ _ _ _ _ _) ; try (intros ; apply path_ishprop).
    - apply tr. exists nil. simpl. done.
    - intros a X Hls.
      strip_truncations. apply tr.
      destruct Hls as [ls Hls].
      exists (cons a ls). intros b. cbn.
      apply (ap (fun z => _ ∨ z) (Hls b)).
  Defined.

  Definition Kf_enumerated : Kf A -> enumerated A.
  Proof.
    intros HKf. apply Kf_unfold in HKf.
    destruct HKf as [X HX].
    pose (ls' := (merely_enumeration_FSet X)).
    simple refine (@Trunc_rec _ _ _ _ _ ls'). clear ls'.
    intros [ls Hls].
    apply tr. exists ls.
    intros a. rewrite <- Hls. apply (HX a).
  Defined.
End fset_dec_enumerated.

Section subobjects.
  Variable A : Type.
  Context `{Univalence}.

  Definition enumeratedS (P : Sub A) : hProp :=
    enumerated (sigT P).

  Lemma enumeratedS_empty : closedEmpty enumeratedS.
  Proof.
    unfold enumeratedS.
    apply tr. exists nil. simpl.
    intros [a Ha]. assumption.
  Defined.

  Lemma enumeratedS_singleton : closedSingleton enumeratedS.
  Proof.
    intros x. apply tr. simpl.
    exists (cons (x;tr idpath) nil).
    intros [y Hxy]. simpl.
    strip_truncations. apply tr.
    left. apply tr.
    apply path_sigma with Hxy.
    simpl. apply path_ishprop.
  Defined.

  Fixpoint weaken_list_r (P Q : Sub A) (ls : list (sigT Q)) : list (sigT (max_L P Q)).
  Proof.
    destruct ls as [|[x Hx] ls].
    - exact nil.
    - apply (cons (x; tr (inr Hx))).
      apply (weaken_list_r _ _ ls).
  Defined.

  Lemma listExt_weaken (P Q : Sub A) (ls : list (sigT Q)) (x : A) (Hx : Q x) :
    listExt ls (x; Hx) -> listExt (weaken_list_r P Q ls) (x; tr (inr Hx)).
  Proof.
    induction ls as [|[y Hy] ls]; simpl.
    - exact idmap.
    - intros Hls.
      strip_truncations; apply tr.
      destruct Hls as [Hxy | Hls].
      + left. strip_truncations. apply tr.
        apply path_sigma_uncurried. simpl.
        exists (Hxy..1). apply path_ishprop.
      + right. apply IHls. assumption.
  Defined.

  Fixpoint concatD {P Q : Sub A}
    (ls : list (sigT P)) (ls' : list (sigT Q)) : list (sigT (max_L P Q)).
  Proof.
    destruct ls as [|[y Hy] ls].
    - apply weaken_list_r. exact ls'.
    - apply (cons (y; tr (inl Hy))).
      apply (concatD _ _ ls ls').
  Defined.

  (* TODO: this proof basically duplicates a similar proof for weaken_list_r *)
  Lemma listExt_concatD_r (P Q : Sub A) (ls : list (sigT P)) (ls' : list (sigT Q)) (x : A) (Hx : P x) :
    listExt ls (x; Hx) -> listExt (concatD ls ls') (x;tr (inl Hx)).
  Proof.
    induction ls as [|[y Hy] ls]; simpl.
    - exact Empty_rec.
    - intros Hls.
      strip_truncations. apply tr.
      destruct Hls as [Hxy | Hls].
      + left. strip_truncations. apply tr.
        apply path_sigma_uncurried. simpl.
        exists (Hxy..1). apply path_ishprop.
      + right. apply IHls. assumption.
  Defined.

  Lemma listExt_concatD_l (P Q : Sub A) (ls : list (sigT P)) (ls' : list (sigT Q)) (x : A) (Hx : Q x) :
    listExt ls' (x; Hx) -> listExt (concatD ls ls') (x;tr (inr Hx)).
  Proof.
    induction ls as [|[y Hy] ls]; simpl.
    - apply listExt_weaken.
    - intros Hls'. apply tr.
      right. apply IHls. assumption.
  Defined.

  Lemma enumeratedS_union (P Q : Sub A) :
    enumeratedS P -> enumeratedS Q -> enumeratedS (max_L P Q).
  Proof.
    intros HP HQ.
    strip_truncations; apply tr.
    destruct HP as [ep HP], HQ as [eq HQ].
    exists (concatD ep eq).
    intros [x Hx].
    strip_truncations.
    destruct Hx as [Hxp | Hxq].
    - apply listExt_concatD_r. apply HP.
    - apply listExt_concatD_l. apply HQ.
  Defined.

  Opaque enumeratedS.
  Definition FSet_to_enumeratedS :
    forall (X : FSet A), enumeratedS (k_finite.map X).
  Proof.
    hinduction.
    - apply enumeratedS_empty.
    - intros a. apply enumeratedS_singleton.
    - unfold k_finite.map; simpl.
      intros X Y Xs Ys.
      apply enumeratedS_union; assumption.
    - intros. apply path_ishprop.
    - intros. apply path_ishprop.
    - intros. apply path_ishprop.
    - intros. apply path_ishprop.
    - intros. apply path_ishprop.
  Defined.
  Transparent enumeratedS.

  Instance hprop_sub_fset (P : Sub A) :
    IsHProp {X : FSet A & k_finite.map X = P}.
  Proof.
    apply hprop_allpath. intros [X HX] [Y HY].
    assert (X = Y) as HXY.
    { apply (isinj_embedding k_finite.map). apply _.
      apply (HX @ HY^). }
    apply path_sigma with HXY.
    apply set_path2.
  Defined.

  Fixpoint list_weaken_to_fset (P : Sub A) (ls : list (sigT P)) : FSet A :=
    match ls with
    | nil => ∅
    | cons x xs => {|x.1|} ∪ (list_weaken_to_fset P xs)
    end.

  Lemma list_weaken_to_fset_ext (P : Sub A) (ls : list (sigT P)) (a : A) (Ha : P a):
    listExt ls (a;Ha) -> a ∈ (list_weaken_to_fset P ls).
  Proof.
    induction ls as [|[x Hx] xs]; simpl.
    - apply idmap.
    - intros Hin.
      strip_truncations. apply tr.
      destruct Hin as [Hax | Hin].
      + left.
        strip_truncations. apply tr.
        exact (Hax..1).
      + right. by apply IHxs.
  Defined.

  Lemma list_weaken_to_fset_in_sub (P : Sub A) (ls : list (sigT P)) (a : A) :
    a ∈ (list_weaken_to_fset P ls) -> P a.
  Proof.
    induction ls as [|[x Hx] xs]; simpl.
    - apply Empty_rec.
    - intros Ha.
      strip_truncations.
      destruct Ha as [Hax | Hin].
      + strip_truncations.
        by rewrite Hax.
      + by apply IHxs.
  Defined.

  Definition enumeratedS_to_FSet :
    forall (P : Sub A), enumeratedS P ->
    {X : FSet A & k_finite.map X = P}.
  Proof.
    intros P HP.
    strip_truncations.
    destruct HP as [ls Hls].
    exists (list_weaken_to_fset _ ls).
    apply path_forall. intro a.
    symmetry. apply path_iff_hprop.
    - intros Ha.
      apply list_weaken_to_fset_ext with Ha.
      apply Hls.
    - unfold k_finite.map.
      apply list_weaken_to_fset_in_sub.
  Defined.
End subobjects.
