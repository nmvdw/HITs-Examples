{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Syntax

module Language where

data Program : Set where
  fail : Program
  exec : Syntax -> State -> Program

postulate
  assignp : (z : State) (x n : Nat) -> exec (x := n) z == exec skip ( z [ x :== n ])
  comp₁ : (z : State) (S : Syntax) -> exec (conc skip S) z == exec S z
  comp₂ : (z z' : State) (S₁ S₂ S₁' : Syntax) -> exec S₁ z == exec S₁' z' -> exec (conc S₁ S₂) z == exec (conc S₁' S₂) z'
  while₁ : (z : State) (x n : Nat) (S : Syntax) -> defined z x -> equals z x n -> exec (while x == n do S) z == exec (conc S (while x == n do S)) z
  while₂ : (z : State) (x n : Nat) (S : Syntax) -> defined z x -> unequals z x n -> exec (while x == n do S) z == exec skip z
  while₃ : (z : State) (x n : Nat) (S : Syntax) -> undefined z x -> exec (while x == n do S) z == fail

Program-elim :
  (Y : Set)
  -> (failY : Y)
  -> (execY : Syntax -> State -> Y)
  -> (assignY : (z : State) (x n : Nat) -> execY (x := n) z == execY skip ( z [ x :== n ]) )
  -> (compY₁ : (z : State) (S : Syntax) -> execY (conc skip S) z == execY S z )
  -> (compY₂ : (z z' : State) (S₁ S₂ S₁' : Syntax) -> execY S₁ z == execY S₁' z' -> execY (conc S₁ S₂) z == execY (conc S₁' S₂) z')
  -> (whileY₁ : (z : State) (x n : Nat) (S : Syntax) -> defined z x -> equals z x n -> execY (while x == n do S) z == execY (conc S (while x == n do S)) z)
  -> (whileY₂ : (z : State) (x n : Nat) (S : Syntax) -> defined z x -> unequals z x n -> execY (while x == n do S) z == execY skip z)
  -> (whileY₃ : (z : State) (x n : Nat) (S : Syntax) -> undefined z x -> execY (while x == n do S) z == failY)
  -> Program -> Y
Program-elim _ failY _     _ _ _ _ _ _ fail = failY
Program-elim _ _     execY _ _ _ _ _ _ (exec s z) = execY s z
