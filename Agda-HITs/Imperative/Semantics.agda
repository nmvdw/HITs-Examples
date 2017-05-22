{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Semantics where

data koe : Set where
    a : koe
    b : koe

postulate
  kek : a ↦ b
  {-# REWRITE kek #-}


Y : koe -> Set
Y a = Nat
Y b = Bool
