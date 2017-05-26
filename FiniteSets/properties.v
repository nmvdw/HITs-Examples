Require Import HoTT HitTactics.
Require Import definition operations.

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
  rewrite Q.
  reflexivity.
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
hinduction; try (intros; apply set_path2).
- reflexivity.
- intro a.
  destruct (dec (a = a)).
  * reflexivity.
  * contradiction (n idpath).
- intros X Y IHX IHY.
  unfold intersection in *.
  rewrite comprehension_or.
  rewrite comprehension_or.
  rewrite IHX.
  rewrite IHY.
  rewrite comprehension_subset.
  rewrite (comm X).
  rewrite comprehension_subset.
  reflexivity.
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
  rewrite comprehension_or.
  rewrite comprehension_or.
  rewrite P.
  rewrite Q.
  rewrite comprehension_subset.
  rewrite (comm X1).
  rewrite comprehension_subset.
  reflexivity.
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
- intros. unfold intersection. (* TODO isIn is simplified too much *)
  rewrite comprehension_or.
  rewrite comprehension_or.
  (* rewrite intersection_La. *)
  admit.
- unfold intersection.
  cbn.
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
  rewrite
  (comm (U (comprehension (fun a : A => (isIn a Z2 || isIn a Y)%Bool) X2)
           (comprehension (fun a : A => (isIn a Z2 || isIn a Y)%Bool) Y)) Y).
  rewrite assoc.
  rewrite P.
  rewrite <- assoc.
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


(* Properties about subset relation. *)
Lemma subsect_intersection `{Funext} (X Y : FSet A) :
			X ⊆ Y = true -> U X Y = Y.
Proof.
hinduction X; try (intros; apply path_forall; intro; apply set_path2).
- intros. apply nl.
- intros a. hinduction Y;
	try (intros; apply path_forall; intro; apply set_path2).
	(*intros. apply equiv_hprop_allpath.*)
	+ intro. cbn.  contradiction (false_ne_true).
	+ intros. destruct (dec (a = a0)).
		rewrite p; apply idem.
		contradiction (false_ne_true).
	+ intros X1 X2 IH1 IH2.
	intro Ho.
	destruct (isIn a X1);
	destruct (isIn a X2).
	specialize (IH1 idpath).
	specialize (IH2 idpath).
	rewrite assoc. rewrite IH1. reflexivity.
	specialize (IH1 idpath).
	rewrite assoc. rewrite IH1. reflexivity.
	specialize (IH2 idpath).
	rewrite assoc. rewrite (comm (L a)). rewrite <- assoc. rewrite IH2.
	reflexivity.
	cbn in Ho. contradiction (false_ne_true).
- intros X1 X2 IH1 IH2 G.
	destruct (subset X1 Y);
	destruct (subset X2 Y).
	specialize (IH1 idpath).
	specialize (IH2 idpath).
	rewrite <- assoc. rewrite IH2. rewrite IH1. reflexivity.
	specialize (IH1 idpath).
	apply IH2 in G.
	rewrite <- assoc. rewrite G. rewrite IH1. reflexivity.
	specialize (IH2 idpath).
	apply IH1 in G.
	rewrite <- assoc. rewrite IH2. rewrite G. reflexivity.
	specialize (IH1 G). specialize (IH2 G).
	rewrite <- assoc. rewrite IH2. rewrite IH1. reflexivity.
Defined.

Theorem

End properties.
