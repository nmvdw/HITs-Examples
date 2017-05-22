{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Expressions where

private
  data Exp' : Set where
    value : Nat -> Exp'
    addition : Exp' -> Exp' -> Exp'

Exp : Set
Exp = Exp'

val : Nat -> Exp
val = value

plus : Exp -> Exp -> Exp
plus = addition

postulate 
  add : (n m : Nat) -> plus (val n) (val m) == val (n + m)
  trunc : is-set Exp

Exp-ind                : (C : Exp -> Set) 
                       -> (vC : (n : Nat) -> C (val n))
                       -> (pC : (e₁ e₂ : Exp) -> C e₁ -> C e₂ -> C(plus e₁ e₂))
                       -> (addC : (n m : Nat) -> PathOver C (add n m) (pC (val n) (val m) (vC n) (vC m)) (vC (n + m)))
                       -> (t : (e : Exp) -> is-set (C e))
                       -> (x : Exp) -> C x
Exp-ind C vC pC addC t (value n)  = vC n
Exp-ind C vC pC addC t (addition e₁ e₂)  = pC e₁ e₂ (Exp-ind C vC pC addC t e₁) (Exp-ind C vC pC addC t e₂)

postulate
  Exp-ind-βadd : (C : Exp -> Set) 
                 -> (vC : (n : Nat) -> C (val n))
                 -> (pC : (e₁ e₂ : Exp) -> C e₁ -> C e₂ -> C(plus e₁ e₂))
                 -> (addC : (n m : Nat) -> PathOver C (add n m) (pC (val n) (val m) (vC n) (vC m)) (vC (n + m)))
                 -> (t : (e : Exp) -> is-set (C e))
                 -> (n m : Nat)
                 -> apd (Exp-ind C vC pC addC t) (add n m) == addC n m

Exp-rec                : {C : Set} 
                       -> (vC : Nat -> C)
                       -> (pC : C -> C -> C)
                       -> (addC : (n m : Nat) -> pC (vC n) (vC m) == vC (n + m))
                       -> (t : is-set C)
                       -> Exp -> C
Exp-rec vC pC addC t (value n)  = vC n
Exp-rec vC pC addC t (addition e₁ e₂)  = pC (Exp-rec vC pC addC t e₁) (Exp-rec vC pC addC t e₂)

postulate
  Exp-rec-βadd : {C : Set} 
                 -> (vC : Nat -> C)
                 -> (pC : C -> C -> C)
                 -> (addC : (n m : Nat) -> pC (vC n) (vC m) == vC (n + m))
                 -> (t : is-set C)
                 -> (n m : Nat)
                 -> ap (Exp-rec vC pC addC t) (add n m) == addC n m
