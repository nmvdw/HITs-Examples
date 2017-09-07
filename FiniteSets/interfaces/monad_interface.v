(** The structure of a monad. *)
Require Import HoTT.

Section functor.
  Variable (F : Type -> Type).
  Context `{Functorish F}.

  Class Functor :=
    {
      fmap_compose {A B C : Type} (f : A -> B) (g : B -> C) :
        fmap F (g o f) = fmap F g o fmap F f
    }.
End functor.
  
Section monad_operations.
  Variable (F : Type -> Type).

  Class hasPure :=
    {
      pure : forall (A : Type), A -> F A
    }.

  Class hasBind :=
    {
      bind : forall (A : Type), F(F A) -> F A
    }.
End monad_operations.

Arguments pure {_} {_} _ _.
Arguments bind {_} {_} _ _.

Section monad.
  Variable (F : Type -> Type).
  Context `{Functor F} `{hasPure F} `{hasBind F}.

  Class Monad :=
    {
      bind_assoc : forall {A : Type},
        bind A o bind (F A) = bind A o fmap F (bind A) ;
      bind_neutral_l : forall {A : Type},
          bind A o pure (F A) = idmap ;
      bind_neutral_r : forall {A : Type},
          bind A o fmap F (pure A) = idmap
    }.
End monad.