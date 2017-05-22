{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Integers where

private
  data Integers : Set where
    z : Integers
    S : Integers -> Integers
    P : Integers -> Integers

Ints : Set
Ints = Integers

nul : Ints
nul = z

Succ : Ints -> Ints
Succ = S

Pred : Ints -> Ints
Pred = P

postulate
  invl : (x : Integers) -> P(S x) == x
  invr : (x : Integers) -> S(P x) == x
  trunc : is-set Ints

Zind : (Y : Integers -> Set)
       -> (zY : Y z)
       -> (SY : (x : Integers) -> Y x -> Y(S x))
       -> (PY : (x : Integers) -> Y x -> Y(P x))
       -> (invYl : (x : Integers) (y : Y x) -> PathOver Y (invl x) (PY (S x) (SY x y)) y)
       -> (invYr : (x : Integers) (y : Y x) -> PathOver Y (invr x) (SY (P x) (PY x y)) y)
       -> (t : (x : Integers) -> is-set (Y x))
       -> (x : Integers) -> Y x
Zind Y zY SY PY invYl invYr t z = zY
Zind Y zY SY PY invYl invYr t (S x) = SY x (Zind Y zY SY PY invYl invYr t x)
Zind Y zY SY PY invYl invYr t (P x) = PY x (Zind Y zY SY PY invYl invYr t x)

postulate
  Zind-βinvl :
    (Y : Integers -> Set)
    -> (zY : Y z)
    -> (SY : (x : Integers) -> Y x -> Y(S x))
    -> (PY : (x : Integers) -> Y x -> Y(P x))
    -> (invYl : (x : Integers) (y : Y x) -> PathOver Y (invl x) (PY (S x) (SY x y)) y)
    -> (invYr : (x : Integers) (y : Y x) -> PathOver Y (invr x) (SY (P x) (PY x y)) y)
    -> (t : (x : Integers) -> is-set (Y x))
    -> (x : Integers)
    -> apd (Zind Y zY SY PY invYl invYr t) (invl x) == invYl x (Zind Y zY SY PY invYl invYr t x)

  Zind-βinvr :
    (Y : Integers -> Set)
    -> (zY : Y z)
    -> (SY : (x : Integers) -> Y x -> Y(S x))
    -> (PY : (x : Integers) -> Y x -> Y(P x))
    -> (invYl : (x : Integers) (y : Y x) -> PathOver Y (invl x) (PY (S x) (SY x y)) y)
    -> (invYr : (x : Integers) (y : Y x) -> PathOver Y (invr x) (SY (P x) (PY x y)) y)
    -> (t : (x : Integers) -> is-set (Y x))
    -> (x : Integers)
    -> apd (Zind Y zY SY PY invYl invYr t) (invr x) == invYr x (Zind Y zY SY PY invYl invYr t x)
