(** Some general prerequisities in homotopy type theory. *)
Require Import HoTT.

Definition squash (A : Type) `{Decidable A} : Type :=
  match dec A with
  | inl _ => Unit
  | inr _ => Empty
  end.

Definition from_squash (A : Type) `{Decidable A} {x : squash A} : A.
Proof.
  unfold squash in *.
  destruct (dec A).
  - apply a.
  - contradiction.
Defined.

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

Definition S1_merely_decidable_equality `{Univalence} : MerelyDecidablePaths S1.
Proof.
  simple refine (S1_ind _ _ _) ; simpl.
  - simple refine (S1_ind _ _ _) ; simpl.
    * apply (inl (tr idpath)).
    * apply path_ishprop.      
  - apply path_forall.
    intro z.
    rewrite transport_forall, transport_sum.
    destruct
      (transportD (fun _ : S1 => S1)
                  (fun x y : S1 => Decidable (Trunc (-1) (x = y)))
                  loop
                  (transport (fun _ : S1 => S1) loop^ z)
                  (S1_ind
                     (fun x : S1 => Decidable (Trunc (-1) (base = x)))
                     (inl (tr 1%path))
                     (transport_sum loop (inl (tr 1))
                                    @
                                    ap inl
                                    (path_ishprop
                                       (transport
                                          (fun a : S1 => Trunc (-1) (base = a))
                                          loop
                                          (tr 1))
                                       (tr 1)
                                    )
                     )
                     (transport (fun _ : S1 => S1) loop^ z)
                  )
      )
      as [t | n].
    ** revert t.
       revert z.
       simple refine (S1_ind (fun _ => _) _ _) ; simpl.
       *** intros.
           apply path_ishprop.
       *** apply path_forall.
           intro z.
           rewrite transport_forall, transport_paths_FlFr, ap_const.
           hott_simpl.
           apply set_path2.
    ** contradiction n.
       rewrite ?transport_const.
       simple refine (S1_ind (fun q => Trunc (-1) (base = q)) _ _ z) ; simpl.
       *** apply (tr idpath).
       *** apply path_ishprop.
Defined.

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