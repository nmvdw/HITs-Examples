{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Syntax where

data Maybe (A : Set) : Set where
  Just : A -> Maybe A
  Nothing : Maybe A

eqN : Nat -> Nat -> Bool
eqN 0 0 = true
eqN 0 _ = false
eqN (S _) 0 = false
eqN (S n) (S m) = eqN n m

-- first coordinate represents the variable x_i, second the value
State : Set
State = List (Nat × Nat)

_[_:==_] : State -> Nat -> Nat -> State
nil [ x :== n ] = (x , n) :: nil
((y , m) :: s) [ x :== n ] =
  if eqN x y
    then (x , n) :: s
    else ((y , m) :: (s [ x :== n ]))

equals : State -> Nat -> Nat -> Set
equals nil _ _ = Empty
equals ((x , n) :: s) y m =
  if eqN x y
    then
      if eqN n m
        then Unit
        else Empty
    else equals s y m

unequals : State -> Nat -> Nat -> Set
unequals nil _ _ = Unit
unequals ((x , n) :: s) y m =
  if eqN x y
    then
      if eqN n m
        then Empty
        else Unit
    else unequals s y m

defined : State -> Nat -> Set
defined nil y = Empty
defined ((x , n) :: s) y =
  if eqN x y
    then Unit
    else defined s y

undefined : State -> Nat -> Set
undefined nil y = Unit
undefined ((x , n) :: s) y =
  if eqN x y
    then Empty
    else undefined s y

data Syntax : Set where
  skip : Syntax
  _:=_ : Nat -> Nat -> Syntax
  conc : Syntax -> Syntax -> Syntax
  while_==_do_ : Nat -> Nat -> Syntax -> Syntax
