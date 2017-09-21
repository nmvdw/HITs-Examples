Require Import HoTT HitTactics.
Require Import kuratowski.operations kuratowski.properties kuratowski.kuratowski_sets.

Section Length.
  Context {A : Type} `{DecidablePaths A} `{Univalence}.
  
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
      destruct (dec (a = b)) as [Hab | Hab].
      + rewrite Hab. simplify_isIn_d. reflexivity.
      + rewrite ?singleton_isIn_d_false; auto.
        ++ simpl. 
           destruct (a ∈_d X), (b ∈_d X) ; reflexivity.
        ++ intro p. contradiction (Hab p^).
  Defined.
End Length.