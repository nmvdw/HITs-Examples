Require Import HoTT HitTactics prelude.
Require Import kuratowski.operations kuratowski.properties kuratowski.kuratowski_sets.

Section Length.
  Context {A : Type} `{MerelyDecidablePaths A} `{Univalence}.
  
  Definition length : FSet A -> nat.
    simple refine (FSet_cons_rec _ _ _ _ _ _).
    - apply 0.
    - intros a X n.
      apply (if a ∈_d X then n else (S n)).
    - intros X a n.
      simpl.
      simplify_isIn_d.
      destruct (dec (a ∈ X)) ; reflexivity.
    - intros X a b n.
      simpl.
      simplify_isIn_d.
      destruct (m_dec_path a b) as [Hab | Hab].
(*      destruct (dec (Trunc (-1) (a = b))) as [Hab | Hab]. *)
      + strip_truncations.
        rewrite Hab. simplify_isIn_d. reflexivity.
      + rewrite ?singleton_isIn_d_false; auto.
        ++ simpl. 
           destruct (a ∈_d X), (b ∈_d X) ; reflexivity.
        ++ intro p. contradiction (Hab (tr p^)).
        ++ intros p.
           apply (Hab (tr p)).          
  Defined.
End Length.