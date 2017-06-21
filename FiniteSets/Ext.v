(** Extensionality of the FSets *)
Require Import HoTT HitTactics.
Require Import definition operations.

Section ext.
Context {A : Type}.
Context {A_deceq : DecidablePaths A}.

Theorem union_idem : forall x: FSet A, U x x = x.
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
Lemma subset_union `{Funext} (X Y : FSet A) : 
  subset X Y = true -> U X Y = Y.
Proof.
hinduction X; try (intros; apply path_forall; intro; apply set_path2).
- intros. apply nl.
- intros a. hinduction Y;
  try (intros; apply path_forall; intro; apply set_path2).
  + intro. contradiction (false_ne_true).
  + intros. destruct (dec (a = a0)).
    rewrite p; apply idem.
    contradiction (false_ne_true).
  + intros X1 X2 IH1 IH2.
    intro Ho.
    destruct (isIn a X1);
      destruct (isIn a X2).
    * specialize (IH1 idpath).
      rewrite assoc. f_ap. 
    * specialize (IH1 idpath).
      rewrite assoc. f_ap. 
    * specialize (IH2 idpath).
      rewrite (comm X1 X2).
      rewrite assoc. f_ap. 
    * contradiction (false_ne_true). 
- intros X1 X2 IH1 IH2 G. 
  destruct (subset X1 Y);
    destruct (subset X2 Y).
  * specialize (IH1 idpath).    
    specialize (IH2 idpath).
    rewrite <- assoc. rewrite IH2. apply IH1. 
  * contradiction (false_ne_true).
  * contradiction (false_ne_true).
  * contradiction (false_ne_true).
Defined.

Lemma subset_union_l `{Funext} X :
  forall Y, subset X (U X Y) = true.
Proof.
hinduction X;
  try (intros; apply path_forall; intro; apply set_path2).
- reflexivity.
- intros a Y. destruct (dec (a = a)).
  * reflexivity.
  * by contradiction n.
- intros X1 X2 HX1 HX2 Y.
  refine (ap (fun z => (X1 ⊆ z && X2 ⊆ (X1 ∪ X2) ∪ Y))%Bool (assoc X1 X2 Y)^ @ _).
  refine (ap (fun z => (X1 ⊆ _ && X2 ⊆ z ∪ Y))%Bool (comm _ _) @ _).
  refine (ap (fun z => (X1 ⊆ _ && X2 ⊆ z))%Bool (assoc _ _ _)^ @ _).
  rewrite HX1. simpl. apply HX2.
Defined.

Lemma subset_union_equiv `{Funext}
  : forall X Y : FSet A, subset X Y = true <~> U X Y = Y.
Proof.
  intros X Y.
  eapply equiv_iff_hprop_uncurried.
  split.
  -  apply subset_union.
  - intros HXY. etransitivity.
    apply (ap _ HXY^).
    apply subset_union_l.
Defined.

Lemma subset_isIn `{FE : Funext} (X Y : FSet A) :
  (forall (a : A), isIn a X = true -> isIn a Y = true)
  <~> (subset X Y = true).
Proof.
  eapply equiv_iff_hprop_uncurried.
  split.
  - hinduction X ; try (intros ; apply path_forall ; intro ; apply set_path2).
    + intros ; reflexivity.
    + intros a H. 
      apply H.
      destruct (dec (a = a)).
      * reflexivity.
      * contradiction (n idpath).
    + intros X1 X2 H1 H2 H.
      enough (subset X1 Y = true).
      rewrite X.
      enough (subset X2 Y = true).
      rewrite X0.
      reflexivity.
      * apply H2.
        intros a Ha.
        apply H.
        rewrite Ha.
        destruct (isIn a X1) ; reflexivity.
      * apply H1.
        intros a Ha.
        apply H.
        rewrite Ha.
        reflexivity.        
  - hinduction X.
    + intros. contradiction (false_ne_true X0).
    + intros b H a.
      destruct (dec (a = b)).
      * intros ; rewrite p ; apply H.
      * intros X ; contradiction (false_ne_true X).
    + intros X1 X2.
      intros IH1 IH2 H1 a H2.
      destruct (subset X1 Y) ; destruct (subset X2 Y);
        cbv in H1; try by contradiction false_ne_true.
      specialize (IH1 idpath a). specialize (IH2 idpath a).
      destruct (isIn a X1); destruct (isIn a X2);
        cbv in H2; try by contradiction false_ne_true.
      by apply IH1.
      by apply IH1.
      by apply IH2.
    + repeat (intro; intros; apply path_forall).
      intros; intro; intros; apply set_path2.
    + repeat (intro; intros; apply path_forall).
      intros; intro; intros; apply set_path2.
    + repeat (intro; intros; apply path_forall).
      intros; intro; intros; apply set_path2.
    + repeat (intro; intros; apply path_forall).
      intros; intro; intros; apply set_path2.
    + repeat (intro; intros; apply path_forall).
      intros; intro; intros; apply set_path2.
Defined.

(** ** Extensionality proof *)

Lemma eq_subset' (X Y : FSet A) : X = Y <~> (U Y X = X) * (U X Y = Y).
Proof.
  unshelve eapply BuildEquiv.
  { intro H. rewrite H. split; apply union_idem. }
  unshelve esplit.
  { intros [H1 H2]. etransitivity. apply H1^.
    rewrite comm. apply H2. }
  intro; apply path_prod; apply set_path2. 
  all: intro; apply set_path2.  
Defined.

Lemma eq_subset `{Funext} (X Y : FSet A) :
  X = Y <~> ((subset Y X = true) * (subset X Y = true)).
Proof.
  transitivity ((U Y X = X) * (U X Y = Y)).
  apply eq_subset'.
  symmetry.
  eapply equiv_functor_prod'; apply subset_union_equiv.
Defined.

Theorem fset_ext `{Funext} (X Y : FSet A) :
  X = Y <~> (forall (a : A), isIn a X = isIn a Y).
Proof.
  etransitivity. apply eq_subset.
  transitivity
    ((forall a, isIn a Y = true -> isIn a X = true)
     *(forall a, isIn a X = true -> isIn a Y = true)).
  - eapply equiv_functor_prod';
    apply equiv_iff_hprop_uncurried;
    split ; apply subset_isIn.
  - apply equiv_iff_hprop_uncurried.
    split.
    * intros [H1 H2 a].
      specialize (H1 a) ; specialize (H2 a).
      destruct (isIn a X).
      + symmetry ; apply (H2 idpath).
      + destruct (isIn a Y).
        { apply (H1 idpath). }
        { reflexivity. }
    * intros H1.
      split ; intro a ; intro H2.
      + rewrite (H1 a).
        apply H2.
      + rewrite <- (H1 a).
        apply H2.
Defined.

(* With extensionality we can prove decidable equality *)
Instance fsets_dec_eq `{Funext} : DecidablePaths (FSet A).
Proof.
  intros X Y.
  apply (decidable_equiv ((subset Y X = true) * (subset X Y = true)) (eq_subset X Y)^-1). (* TODO: this is so slow?*)
  destruct (Y ⊆ X), (X ⊆ Y).
  - left. refine (idpath, idpath).
  - right. refine (false_ne_true o snd).
  - right. refine (false_ne_true o fst).
  - right. refine (false_ne_true o fst).
Defined.

End ext.
