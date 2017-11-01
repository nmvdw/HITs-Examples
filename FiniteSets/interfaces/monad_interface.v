(** The structure of a monad. *)
(* TODO REMOVE THIS *)
Require Import HoTT.
Require Export HoTT.Classes.interfaces.monad.

Section functor.
  Variable (F : Type -> Type).
  Context `{Functorish F}.

  Class Functor :=
    {
      fmap_compose {A B C : Type} (f : A -> B) (g : B -> C) :
        fmap F (g o f) = fmap F g o fmap F f
    }.
End functor.

Section monad_join.
  Context `{Monad M}.

  Definition mjoin {A} (m : M (M A)) : M A := bind m id.
End monad_join.
