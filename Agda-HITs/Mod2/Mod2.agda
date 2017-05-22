{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Mod2 where

private
  data M' : Set where
    Zero : M'
    S  : M' -> M'

M : Set
M = M'

z : M
z = Zero

Succ : M -> M
Succ = S

postulate 
  mod : (n : M) -> n == Succ(Succ n)
  trunc : is-set M

M-ind                : (C : M -> Set) 
                       -> (a : C Zero)
                       -> (sC : (x : M) -> C x -> C (S x))
                       -> (p : (n : M) (c : C n) -> PathOver C (mod n) c (sC (Succ n) (sC n c)))
                       -> (t : (m : M) -> is-set (C m))
                       -> (x : M) -> C x
M-ind C a sC _ t Zero  = a
M-ind C a sC p t (S x) = sC x (M-ind C a sC p t x)

postulate
  M-ind-βmod : (C : M -> Set) 
         -> (a : C Zero)
         -> (sC : (x : M) -> C x -> C (S x))
         -> (p : (n : M) (c : C n) -> PathOver C (mod n) c (sC (Succ n) (sC n c)))
         -> (t : (m : M)  -> is-set (C m))
         -> (n : M)
         -> apd (M-ind C a sC p t) (mod n) == p n (M-ind C a sC p t n)

M-rec                : {C : Set} 
                       -> (a : C)
                       -> (sC : C -> C)
                       -> (p : (c : C) -> c == sC (sC c))
                       -> (t : is-set C)
                       -> M -> C
M-rec a sC _ _ Zero  = a
M-rec a sC p t (S x) = sC (M-rec a sC p t x)

postulate
  M-rec-βmod : {C : Set} 
         -> (a : C)
         -> (sC : C -> C)
         -> (p : (c : C) -> c == sC (sC c))
         -> (t : is-set C)
         -> (n : M)
         -> ap (M-rec a sC p t) (mod n) == p (M-rec a sC p t n)
