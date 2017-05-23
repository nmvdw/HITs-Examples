Require Import HoTT.
Require Export HoTT.

Module Export definition.
 
Section FSet.
Variable A : Type.

Private Inductive FSet : Type :=
  | E : FSet
  | L : A -> FSet
  | U : FSet -> FSet -> FSet.

Notation "{| x |}" :=  (L x).
Infix "∪" := U (at level 8, right associativity).
Notation "∅" := E.

Axiom assoc : forall (x y z : FSet ),
  x ∪ (y ∪ z) = (x ∪ y) ∪ z.

Axiom comm : forall (x y : FSet),
  x ∪ y = y ∪ x.

Axiom nl : forall (x : FSet),
  ∅ ∪ x = x.

Axiom nr : forall (x : FSet),
  x ∪ ∅ = x.

Axiom idem : forall (x : A),
  {| x |} ∪ {|x|} = {|x|}.

Axiom trunc : IsHSet FSet.

Fixpoint FSet_rec
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : FSet)
  {struct x}
  : P
  := (match x return _ -> _ -> _ -> _ -> _ -> _ -> P with
        | E => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => e
        | L a => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => l a
        | U y z => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => u 
           (FSet_rec P H e l u assocP commP nlP nrP idemP y)
           (FSet_rec P H e l u assocP commP nlP nrP idemP z)
      end) assocP commP nlP nrP idemP H.

Axiom FSet_rec_beta_assoc : forall
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x y z : FSet),
  ap (FSet_rec P H e l u assocP commP nlP nrP idemP) (assoc x y z) 
  =
  (assocP (FSet_rec P H e l u assocP commP nlP nrP idemP x)
          (FSet_rec P H e l u assocP commP nlP nrP idemP y)
          (FSet_rec P H e l u assocP commP nlP nrP idemP z)
  ).

Axiom FSet_rec_beta_comm : forall
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x y : FSet),
  ap (FSet_rec P H e l u assocP commP nlP nrP idemP) (comm x y)
  =
  (commP (FSet_rec P H e l u assocP commP nlP nrP idemP x)
         (FSet_rec P H e l u assocP commP nlP nrP idemP y)
  ).

Axiom FSet_rec_beta_nl : forall
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : FSet),
  ap (FSet_rec P H e l u assocP commP nlP nrP idemP) (nl x)
  =
  (nlP (FSet_rec P H e l u assocP commP nlP nrP idemP x)
  ).

Axiom FSet_rec_beta_nr : forall
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : FSet),
  ap (FSet_rec P H e l u assocP commP nlP nrP idemP) (nr x)
  =
  (nrP (FSet_rec P H e l u assocP commP nlP nrP idemP x)
  ).

Axiom FSet_rec_beta_idem : forall
  (P : Type)
  (H: IsHSet P)
  (e : P)
  (l : A -> P)
  (u : P -> P -> P)
  (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
  (commP : forall (x y : P), u x y = u y x)
  (nlP : forall (x : P), u e x = x)
  (nrP : forall (x : P), u x e = x)
  (idemP : forall (x : A), u (l x) (l x) = l x)
  (x : A),
  ap (FSet_rec P H e l u assocP commP nlP nrP idemP) (idem x)
  =
  idemP x.

End FSet.
Section FSet_induction.
Arguments E {_}.
Arguments U {_} _ _.
Arguments L {_} _.
Arguments assoc {_} _ _ _.
Arguments comm {_} _ _.
Arguments nl {_} _.
Arguments nr {_} _.
Arguments idem {_} _.
Variable A: Type.
Variable  (P : FSet A -> Type).
Variable  (H :  forall a : FSet A, IsHSet (P a)).
Variable  (eP : P E).
Variable  (lP : forall a: A, P (L a)).
Variable  (uP : forall (x y: FSet A), P x -> P y -> P (U x y)).
Variable  (assocP : forall (x y z : FSet A) 
                   (px: P x) (py: P y) (pz: P z),
  assoc x y z #
   (uP      x    (U y z)          px        (uP y z py pz)) 
  = 
   (uP   (U x y)    z       (uP x y px py)          pz)).
Variable  (commP : forall (x y: FSet A) (px: P x) (py: P y),
  comm x y #
  uP x y px py = uP y x py px).
Variable  (nlP : forall (x : FSet A) (px: P x), 
  nl x # uP E x eP px = px).
Variable  (nrP : forall (x : FSet A) (px: P x), 
  nr x # uP x E px eP = px).
Variable  (idemP : forall (x : A), 
  idem x # uP (L x) (L x) (lP x) (lP x) = lP x).

(* Induction principle *)
Fixpoint FSet_ind
  (x : FSet A)
  {struct x}
  : P x
  := (match x return _ -> _ -> _ -> _ -> _ -> _ -> P x with
        | E => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => eP
        | L a => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => lP a
        | U y z => fun _ => fun _ => fun _ => fun _ => fun _ => fun _ => uP y z
           (FSet_ind y)
           (FSet_ind z)
      end) H assocP commP nlP nrP idemP.


Axiom FSet_ind_beta_assoc : forall (x y z : FSet A),
  apD FSet_ind (assoc x y z) =
  (assocP x y z (FSet_ind x)  (FSet_ind y) (FSet_ind z)).

Axiom FSet_ind_beta_comm : forall (x y : FSet A),
  apD FSet_ind (comm x y) = (commP x y (FSet_ind x) (FSet_ind y)).

Axiom FSet_ind_beta_nl : forall (x : FSet A),
  apD FSet_ind (nl x) = (nlP x (FSet_ind x)).

Axiom FSet_ind_beta_nr : forall (x : FSet A),
  apD FSet_ind (nr x) = (nrP x (FSet_ind x)).

Axiom FSet_ind_beta_idem : forall (x : A), apD FSet_ind (idem x) = idemP x.


End FSet_induction.
End definition.