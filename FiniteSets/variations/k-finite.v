Require Import HoTT HitTactics.
Require Import lattice representations.definition fsets.operations extensionality.

Definition Sub A := A -> hProp.

Section k_finite.

  Context {A : Type}.
  Context `{Univalence}.
  
  Instance subA_set : IsHSet (Sub A).
  Proof.
    apply _.
  Defined.  
  
  Definition map : FSet A -> Sub A.
  Proof.
    unfold Sub.
    intros X a.
    apply (isIn a X).
  Defined.

  Definition k_finite (B : Sub A) : hProp.
  Proof.
    simple refine (@BuildhProp (@sig (FSet A) (fun X => B = map X)) _).
    apply hprop_allpath.
    unfold map.
    intros [X PX] [Y PY].
    assert (X0 : (fun a : A => a ∈ X) = (fun a : A => a ∈ Y)).
    {
      transitivity B.
      - symmetry ; apply PX.
      - apply PY.
    }
    assert (X = Y).
    {
      apply fset_ext.
      intro a.
      refine (ap (fun f : A -> hProp => f a) X0).
    }
    apply path_sigma_uncurried.
    exists X1.
    apply set_path2.
  Defined.  

End k_finite.
