(** Some general prerequisities in homotopy type theory. *)
Require Import HoTT.

Lemma ap_inl_path_sum_inl {A B} (x y : A) (p : inl x = inl y) :
  ap inl (path_sum_inl B p) = p.
Proof.
  transitivity (@path_sum _ B (inl x) (inl y) (path_sum_inl B p));
    [ | apply (eisretr_path_sum _) ].
  destruct (path_sum_inl B p).
  reflexivity.
Defined.

Lemma ap_equiv {A B} (f : A <~> B) {x y : A} (p : x = y) :
  ap (f^-1 o f) p = eissect f x @ p @ (eissect f y)^.
Proof.
  destruct p.
  hott_simpl.
Defined.

Global Instance hprop_lem `{Univalence} (T : Type) (Ttrunc : IsHProp T) : IsHProp (T + ~T).
Proof.
  apply (equiv_hprop_allpath _)^-1.
  intros [x | nx] [y | ny] ; try f_ap ; try (apply Ttrunc) ; try contradiction.
  - apply equiv_hprop_allpath. apply _.
Defined.

Global Instance inl_embedding (A B : Type) : IsEmbedding (@inl A B).
Proof.
  - intros [x1 | x2].
    * apply ishprop_hfiber_inl.
    * intros [z p].
      contradiction (inl_ne_inr _ _ p).
Defined.

Global Instance inr_embedding (A B : Type) : IsEmbedding (@inr A B).
Proof.
  - intros [x1 | x2].
    * intros [z p].
      contradiction (inr_ne_inl _ _ p).
    * apply ishprop_hfiber_inr.
Defined.

Class MerelyDecidablePaths A :=
  m_dec_path : forall (a b : A), Decidable(Trunc (-1) (a = b)).

Global Instance DecidableToMerely A (H : DecidablePaths A) : MerelyDecidablePaths A.
Proof.
  intros x y.
  destruct (dec (x = y)).
  - apply (inl(tr p)).
  - refine (inr(fun p => _)).
    strip_truncations.
    apply (n p).
Defined.

Section merely_decidable_operations.
  Variable (A B : Type).
  Context `{MerelyDecidablePaths A} `{MerelyDecidablePaths B}.
  
  Global Instance merely_decidable_paths_prod : MerelyDecidablePaths(A * B).
  Proof.
    intros x y.
    destruct (m_dec_path (fst x) (fst y)) as [p1 | n1],
             (m_dec_path (snd x) (snd y)) as [p2 | n2].
    - apply inl.
      strip_truncations.
      apply tr.
      apply path_prod ; assumption.
    - apply inr.
      intros pp.
      strip_truncations.
      apply (n2 (tr (ap snd pp))).
    - apply inr.
      intros pp.
      strip_truncations.
      apply (n1 (tr (ap fst pp))).
    - apply inr.
      intros pp.
      strip_truncations.
      apply (n1 (tr (ap fst pp))).
  Defined.  

  Global Instance merely_decidable_sum : MerelyDecidablePaths (A + B).
  Proof.
    intros [x1 | x2] [y1 | y2].
    - destruct (m_dec_path x1 y1) as [t | n].
      * apply inl.
        strip_truncations.
        apply (tr(ap inl t)).
      * refine (inr(fun p => _)).
        strip_truncations.
        refine (n(tr _)).
        refine (path_sum_inl _ p).
    - refine (inr(fun p => _)).
      strip_truncations.
      refine (inl_ne_inr x1 y2 p).
    - refine (inr(fun p => _)).
      strip_truncations.
      refine (inr_ne_inl x2 y1 p).
    - destruct (m_dec_path x2 y2) as [t | n].
      * apply inl.
        strip_truncations.
        apply (tr(ap inr t)).
      * refine (inr(fun p => _)).
        strip_truncations.
        refine (n(tr _)).
        refine (path_sum_inr _ p).
  Defined.
End merely_decidable_operations.