{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Expressions

module Thms where

value : (e : Exp) -> Σ Nat (\n -> e == val n)
value = Exp-ind
  (\e ->  Σ Nat (\n -> e == val n))
  (\n -> n , idp)
  (\e₁ e₂ v₁ v₂  -> fst v₁ + fst v₂ ,
    (ap (\e -> plus e e₂) (snd v₁) ∙ ap (plus (val (fst v₁))) (snd v₂)) ∙ add (fst v₁) (fst v₂)
  )
  (\n m -> from-transp! (\e -> Σ Nat (\n -> e == val n)) (add n m) (pair= {!!} {!!}))
  (\e -> {!!})
