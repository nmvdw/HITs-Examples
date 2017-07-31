Require Import HoTT.

Definition lor (X Y : hProp) : hProp := BuildhProp (Trunc (-1) (sum X Y)).

Infix "\/" := lor.

Section lor_props.
  Variable X Y Z : hProp.
  Context `{Univalence}.

  Theorem lor_assoc : (X \/ (Y \/ Z)) = ((X \/ Y) \/ Z).
  Proof.
    apply path_iff_hprop ; cbn.
    * simple refine (Trunc_ind _ _).
      intros [x | yz] ; cbn.
      + apply (tr (inl (tr (inl x)))).
      + simple refine (Trunc_ind _ _ yz).
        intros [y | z].
        ++ apply (tr (inl (tr (inr y)))). 
        ++ apply (tr (inr z)).
    * simple refine (Trunc_ind _ _).
      intros [xy | z] ; cbn.
      + simple refine (Trunc_ind _ _ xy).
        intros [x | y].
        ++ apply (tr (inl x)). 
        ++ apply (tr (inr (tr (inl y)))).
      + apply (tr (inr (tr (inr z)))).
  Defined.

  Theorem lor_comm : (X \/ Y) = (Y \/ X).
  Proof.
    apply path_iff_hprop ; cbn.
    * simple refine (Trunc_ind _ _).
      intros [x | y].
      + apply (tr (inr x)).
      + apply (tr (inl y)).
    * simple refine (Trunc_ind _ _).
      intros [y | x].
      + apply (tr (inr y)).
      + apply (tr (inl x)).
  Defined.

  Theorem lor_nl : (False_hp \/ X) = X.
  Proof.
    apply path_iff_hprop ; cbn.
    * simple refine (Trunc_ind _ _).
      intros [ | x].
      + apply Empty_rec.
      + apply x.
    * apply (fun x => tr (inr x)).
  Defined.

  Theorem lor_nr : (X \/ False_hp) = X.
  Proof.
    apply path_iff_hprop ; cbn.
    * simple refine (Trunc_ind _ _).
      intros [x | ].
      + apply x.
      + apply Empty_rec.
    * apply (fun x => tr (inl x)).
  Defined.

  Theorem lor_idem : (X \/ X) = X.
  Proof.
    apply path_iff_hprop ; cbn.
    - simple refine (Trunc_ind _ _).
      intros [x | x] ; apply x.
    - apply (fun x => tr (inl x)).
  Defined.

End lor_props.
