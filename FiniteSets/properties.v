Require Import HoTT HitTactics.
Require Export definition operations.

Section properties.

Context {A : Type}.
Context {A_deceq : DecidablePaths A}.

(** union properties *)
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

  
(** isIn properties *)
Lemma isIn_singleton_eq (a b: A) : isIn a  (L b) = true -> a = b.
Proof. unfold isIn. simpl. 
destruct (dec (a = b)). intro. apply p.
intro X. 
contradiction (false_ne_true X).
Defined.

Lemma isIn_empty_false (a: A) : isIn a E = true -> Empty.
Proof. 
cbv. intro X.
contradiction (false_ne_true X). 
Defined.

Lemma isIn_union (a: A) (X Y: FSet A) : 
	    isIn a (U X Y) = (isIn a X || isIn a Y)%Bool.
Proof. reflexivity. Qed. 

(** comprehension properties *)
Lemma comprehension_false Y : comprehension (fun a => isIn a E) Y = E.
Proof.
hrecursion Y; try (intros; apply set_path2).
- cbn. reflexivity.
- cbn. reflexivity.
- intros x y IHa IHb.
  cbn.
  rewrite IHa.
  rewrite IHb.
  rewrite nl.
  reflexivity.
Defined.

Theorem comprehension_or : forall ϕ ψ (x: FSet A),
    comprehension (fun a => orb (ϕ a) (ψ a)) x = U (comprehension ϕ x) 
    (comprehension ψ x).
Proof.
intros ϕ ψ.
hinduction; try (intros; apply set_path2). 
- cbn. symmetry ; apply nl.
- cbn. intros.
  destruct (ϕ a) ; destruct (ψ a) ; symmetry.
  * apply idem.
  * apply nr. 
  * apply nl.
  * apply nl.
- simpl. intros x y P Q.
  cbn. 
  rewrite P.
  rewrite Q.
  rewrite <- assoc.
  rewrite (assoc  (comprehension ψ x)).
  rewrite (comm  (comprehension ψ x) (comprehension ϕ y)).
  rewrite <- assoc.
  rewrite <- assoc.
  reflexivity.
Defined.

Theorem comprehension_subset : forall ϕ (X : FSet A),
    U (comprehension ϕ X) X = X.
Proof.
intros ϕ.
hrecursion; try (intros ; apply set_path2) ; cbn.
- apply nl.
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

(** intersection properties *)
Lemma intersection_0l: forall X: FSet A, intersection E X = E.
Proof.       
hinduction; 
try (intros ; apply set_path2).
- reflexivity.
- intro a.
  reflexivity.
- unfold intersection.
  intros x y P Q.
  cbn.
  rewrite P.
  rewrite Q.
  apply nl.
Defined.

Lemma intersection_0r (X: FSet A): intersection X E = E.
Proof. exact idpath. Defined.

Theorem intersection_La : forall (a : A) (X : FSet A),
    intersection (L a) X = if isIn a X then L a else E.
Proof.
intro a.
hinduction; try (intros ; apply set_path2).
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
  intros x y P Q.
  cbn.
  rewrite P.
  rewrite Q.
  destruct (isIn a x) ; destruct (isIn a y).
  * apply idem.
  * apply nr.
  * apply nl. 
  * apply nl.
Defined.

Lemma intersection_comm X Y: intersection X Y = intersection Y X.
Proof.
hrecursion X;  try (intros; apply set_path2).
- cbn. unfold intersection. apply comprehension_false.
- cbn. unfold intersection. intros a.
  hrecursion Y; try (intros; apply set_path2).
  + cbn. reflexivity.
  + cbn. intros b.
    destruct  (dec (a = b)) as [pa|npa].
    * rewrite pa.
      destruct (dec (b = b)) as [|nb]; [reflexivity|].
      by contradiction nb.
    * destruct (dec (b = a)) as [pb|]; [|reflexivity].
      by contradiction npa.
  + cbn -[isIn]. intros Y1 Y2 IH1 IH2.
    rewrite IH1. 
    rewrite IH2.
    symmetry.
    apply (comprehension_or (fun a => isIn a Y1) (fun a => isIn a Y2) (L a)).
- intros X1 X2 IH1 IH2.
  cbn.
  unfold intersection in *.
  rewrite <- IH1.
  rewrite <- IH2. 
  apply comprehension_or.
Defined.

Theorem intersection_idem : forall (X : FSet A), intersection X X = X.
Proof.
hinduction; try (intros ; apply set_path2).
- reflexivity.
- intro a.
  destruct (dec (a = a)).
  * reflexivity.
  * contradiction (n idpath).
- intros X Y IHX IHY.
  f_ap;
  unfold intersection in *.
  + transitivity (U (comprehension (fun a => isIn a X) X) (comprehension (fun a => isIn a Y) X)).
    apply comprehension_or.
    rewrite IHX.
    rewrite (comm X).    
    apply comprehension_subset.
  + transitivity (U (comprehension (fun a => isIn a X) Y) (comprehension (fun a => isIn a Y) Y)).
    apply comprehension_or.
    rewrite IHY.
    apply comprehension_subset.
Defined.

(** assorted lattice laws *)
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

Theorem distributive_intersection_U (X1 X2 Y : FSet A) :
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
  unfold intersection in *.
  cbn.
  rewrite comprehension_or.
  rewrite comprehension_or.
  reflexivity.
Defined.

Theorem intersection_isIn : forall a (x y: FSet A),
    isIn a (intersection x y) = andb (isIn a x) (isIn a y).
Proof.
intros a x y.
hinduction x; try (intros ; apply set_path2) ; cbn.
- rewrite intersection_0l.
  reflexivity.
- intro b.
  rewrite intersection_La.
  destruct (dec (a = b)) ; cbn.
  * rewrite p.
    destruct (isIn b y).
    + cbn.
      destruct (dec (b = b)); [reflexivity|].
      by contradiction n.
    + reflexivity.
  * destruct (isIn b y).
    + cbn.
      destruct (dec (a = b)); [|reflexivity].
      by contradiction n.
    + reflexivity.
- intros X1 X2 P Q.
  rewrite distributive_intersection_U.
  cbn.
  rewrite P.
  rewrite Q.
  destruct (isIn a X1) ; destruct (isIn a X2) ; destruct (isIn a y) ; 
  reflexivity.
Defined.

Theorem intersection_assoc (X Y Z: FSet A) :
    intersection X (intersection Y Z) = intersection (intersection X Y) Z.
Proof.
hinduction X; try (intros ; apply set_path2).
- cbn.
  rewrite intersection_0l.
  rewrite intersection_0l.
  rewrite intersection_0l.
  reflexivity.
- intros a.
  cbn.
  rewrite intersection_La.
  rewrite intersection_La.
  rewrite intersection_isIn.
  destruct (isIn a Y).
  * rewrite intersection_La.
    destruct (isIn a Z).
    + reflexivity.
    + reflexivity.
  * rewrite intersection_0l.
    reflexivity.      
- unfold intersection. cbn.
  intros X1 X2 P Q.
  rewrite comprehension_or.
  rewrite P.
  rewrite Q.
  rewrite comprehension_or.
  cbn.
  rewrite comprehension_or.
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

  
Theorem distributive_U_int (X1 X2 Y : FSet A) :
    U (intersection X1 X2) Y = intersection (U X1 Y) (U X2 Y).
Proof.
hinduction X1; try (intros ; apply set_path2) ; cbn.
- rewrite intersection_0l.
  rewrite nl.
  unfold intersection.
  rewrite comprehension_all.
  pose (intersection_comm Y X2).
  unfold intersection in p.
  rewrite p.
  rewrite comprehension_subset.
  reflexivity.
- intros.
  assert (Y = intersection (U (L a) Y) Y) as HY.
  { unfold intersection. symmetry.
    transitivity (U (comprehension (fun x => isIn x (L a)) Y) (comprehension (fun x => isIn x Y) Y)).
    apply comprehension_or.
    rewrite comprehension_all.
    apply comprehension_subset. }
  rewrite <- HY.
  admit.
- unfold intersection.
  intros Z1 Z2 P Q.
  rewrite comprehension_or.
  assert (U (U (comprehension (fun a : A => isIn a Z1) X2) 
  	(comprehension (fun a : A => isIn a Z2) X2))
    Y = U (U (comprehension (fun a : A => isIn a Z1) X2) 
  (comprehension (fun a : A => isIn a Z2) X2))
    (U Y Y)).
    rewrite (union_idem Y).
    reflexivity.
  rewrite X.
  rewrite <- assoc.
  rewrite (assoc (comprehension (fun a : A => isIn a Z2) X2)).
  rewrite Q.
  cbn.
  rewrite 
  (comm (U (comprehension (fun a : A => (isIn a Z2 || isIn a Y)%Bool) X2)
           (comprehension (fun a : A => (isIn a Z2 || isIn a Y)%Bool) Y)) Y).
  rewrite assoc.
  rewrite P.
  rewrite <- assoc. cbn.
  rewrite (assoc (comprehension (fun a : A => (isIn a Z1 || isIn a Y)%Bool) Y)).
  rewrite (comm (comprehension (fun a : A => (isIn a Z1 || isIn a Y)%Bool) Y)).
  rewrite <- assoc.
  rewrite assoc.
  enough (C : (U (comprehension (fun a : A => (isIn a Z1 || isIn a Y)%Bool) X2)
             (comprehension (fun a : A => (isIn a Z2 || isIn a Y)%Bool) X2)) 
 = (comprehension (fun a : A => (isIn a Z1 || isIn a Z2 || isIn a Y)%Bool) X2)).
  rewrite C. 
  enough (D :  (U (comprehension (fun a : A => (isIn a Z1 || isIn a Y)%Bool) Y)
                  (comprehension (fun a : A => (isIn a Z2 || isIn a Y)%Bool) Y)) 
 = (comprehension (fun a : A => (isIn a Z1 || isIn a Z2 || isIn a Y)%Bool) Y)).
  rewrite D.
  reflexivity.
  * repeat (rewrite comprehension_or).
    rewrite <- assoc.
    rewrite (comm (comprehension (fun a : A => isIn a Y) Y)).
    rewrite <- (assoc (comprehension (fun a : A => isIn a Z2) Y)).
    rewrite union_idem.
    rewrite assoc.
    reflexivity.
  * repeat (rewrite comprehension_or).
    rewrite <- assoc.
    rewrite (comm (comprehension (fun a : A => isIn a Y) X2)).
    rewrite <- (assoc (comprehension (fun a : A => isIn a Z2) X2)).
    rewrite union_idem.
    rewrite assoc.
    reflexivity.
Admitted.

Theorem absorb_0 (X Y : FSet A) : U X (intersection X Y) = X.
Proof.
hinduction X; try (intros ; apply set_path2) ; cbn.
- rewrite nl.
  apply intersection_0l.
- intro a.
  rewrite intersection_La.
  destruct (isIn a Y).
  * apply union_idem.
  * apply nr.
- intros X1 X2 P Q.
  rewrite distributive_intersection_U.
  rewrite <- assoc.
  rewrite (comm X2).
  rewrite assoc.
  rewrite assoc.
  rewrite P.
  rewrite <- assoc.
  rewrite (comm _ X2).
  rewrite Q.
  reflexivity.
Defined.

Theorem absorb_1 (X Y : FSet A) : intersection X (U X Y) = X.
Proof.
hrecursion X; try (intros ; apply set_path2).
- cbn.
  rewrite nl.
  apply comprehension_false.
- intro a.
  rewrite intersection_La.
  destruct (dec (a = a)).
  * destruct (isIn a Y).
    + apply union_idem.
    + apply nr.
  * contradiction (n idpath).
- intros X1 X2 P Q.
  cbn in *.
  symmetry.
  rewrite <- P.
  rewrite <- Q.
Admitted.

Theorem union_isIn (X Y : FSet A) (a : A) : isIn a (U X Y) = orb (isIn a X) (isIn a Y).
Proof.
reflexivity.  
Defined.

(* Properties about subset relation. *)
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

Lemma eq1 (X Y : FSet A) : X = Y <~> (U Y X = X) * (U X Y = Y).
Proof.
  unshelve eapply BuildEquiv.
  { intro H. rewrite H. split; apply union_idem. }
  unshelve esplit.
  { intros [H1 H2]. etransitivity. apply H1^.
    rewrite comm. apply H2. }
  intro; apply path_prod; apply set_path2. 
  all: intro; apply set_path2.  
Defined.


Lemma subset_union_l `{Funext} X :
  forall Y, subset X (U X Y) = true.
hinduction X;
  try (intros; apply path_forall; intro; apply set_path2).
- reflexivity.
- intros a Y. destruct (dec (a = a)).
  * reflexivity.
  * by contradiction n.
- intros X1 X2 HX1 HX2 Y.
  enough (subset X1 (U (U X1 X2) Y) = true).
  enough (subset X2 (U (U X1 X2) Y) = true).
  rewrite X. rewrite X0. reflexivity.
  { rewrite (comm X1 X2).
    rewrite <- (assoc X2 X1 Y).
    apply (HX2 (U X1 Y)). }
  { rewrite <- (assoc X1 X2 Y). apply (HX1 (U X2 Y)). }
Defined.

Lemma subset_union_equiv `{Funext}
  : forall X Y : FSet A, subset X Y = true <~> U X Y = Y.
Proof.
  intros X Y.
  unshelve eapply BuildEquiv.
  apply subset_union.
  unshelve esplit.
  { intros HXY. rewrite <- HXY. clear HXY.
    apply subset_union_l. }
  all: intro; apply set_path2.
Defined.

Lemma eq_subset `{Funext} (X Y : FSet A) :
  X = Y <~> ((subset Y X = true) * (subset X Y = true)).
Proof.
  transitivity ((U Y X = X) * (U X Y = Y)).
  apply eq1.
  symmetry.
  eapply equiv_functor_prod'; apply subset_union_equiv.
Defined.

Lemma subset_isIn `{FE : Funext} (X Y : FSet A) :
  (forall (a : A), isIn a X = true -> isIn a Y = true)
  <-> (subset X Y = true).
Proof.
  split.
  - hinduction X ; try (intros ; apply path_forall ; intro ; apply set_path2).
    * intros ; reflexivity.
    * intros a H. 
      apply H.
      destruct (dec (a = a)).
      + reflexivity.
      + contradiction (n idpath).
    * intros X1 X2 H1 H2 H.
      enough (subset X1 Y = true).
      rewrite X.
      enough (subset X2 Y = true).
      rewrite X0.
      reflexivity.
      + apply H2.
        intros a Ha.
        apply H.
        rewrite Ha.
        destruct (isIn a X1) ; reflexivity.
      + apply H1.
        intros a Ha.
        apply H.
        rewrite Ha.
        reflexivity.        
  - hinduction X .
    * intros. contradiction (false_ne_true X0).
    * intros b H a.
      destruct (dec (a = b)).
      + intros ; rewrite p ; apply H.
      + intros X ; contradiction (false_ne_true X).
        * intros X1 X2.
          intros IH1 IH2 H1 a H2.
          destruct (subset X1 Y) ; destruct (subset X2 Y);
            cbv in H1; try by contradiction false_ne_true.
          specialize (IH1 idpath a). specialize (IH2 idpath a).
          destruct (isIn a X1); destruct (isIn a X2);
            cbv in H2; try by contradiction false_ne_true.
          by apply IH1.
          by apply IH1.
          by apply IH2.
        * repeat (intro; intros; apply path_forall).
          intros; intro; intros; apply set_path2.
        * repeat (intro; intros; apply path_forall).
          intros; intro; intros; apply set_path2.
        * repeat (intro; intros; apply path_forall).
          intros; intro; intros; apply set_path2.
        * repeat (intro; intros; apply path_forall).
          intros; intro; intros; apply set_path2.
        * repeat (intro; intros; apply path_forall);
          intros; intro; intros; apply set_path2.
Defined.

Lemma HPropEquiv (X Y : Type) (P : IsHProp X) (Q : IsHProp Y) :
  (X <-> Y) -> (X <~> Y).
Proof.
intros [f g].
simple refine (BuildEquiv _ _ _ _).  
apply f.
simple refine (BuildIsEquiv _ _ _ _ _ _ _).
- apply g.
- unfold Sect.
  intro x.  
  apply Q.
- unfold Sect.
  intro x.
  apply P.
- intros.
  apply set_path2.
Defined.

Theorem fset_ext `{Funext} (X Y : FSet A) :
  X = Y <~> (forall (a : A), isIn a X = isIn a Y).
Proof.
  etransitivity. apply eq_subset.
  transitivity
    ((forall a, isIn a Y = true -> isIn a X = true)
     *(forall a, isIn a X = true -> isIn a Y = true)).
  - eapply equiv_functor_prod'.
    apply HPropEquiv.
    exact _.
    exact _.
    split ; apply subset_isIn.
    apply HPropEquiv.
    exact _.
    exact _.
    split ; apply subset_isIn.
  - apply HPropEquiv.
    exact _.
    exact _.
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

End properties. 
