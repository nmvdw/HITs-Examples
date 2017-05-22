{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Interval where

postulate
  I : Set
  z : I
  o : I
  s : z == o
  I-ind : (Y : I -> Set)
          (zY : Y z)
          (oY : Y o)
          (sY : PathOver Y s zY oY)
          (x : I)
          -> Y x
  I-ind-βz : (Y : I -> Set)
             (zY : Y z)
             (oY : Y o)
             (sY : PathOver Y s zY oY)
             -> I-ind Y zY oY sY z ↦ zY
  {-# REWRITE I-ind-βz #-}
  I-ind-βo : (Y : I -> Set)
             (zY : Y z)
             (oY : Y o)
             (sY : PathOver Y s zY oY)
             -> I-ind Y zY oY sY o ↦ oY
  {-# REWRITE I-ind-βo #-}
  I-ind-βs : (Y : I -> Set)
             (zY : Y z)
             (oY : Y o)
             (sY : PathOver Y s zY oY)
             -> apd (I-ind Y zY oY sY) s == sY

transp-cst : (A : Set) {x y : A} (B : Set) (p : x == y) (z : B) -> transport (\x -> B) p z == z
transp-cst A B idp z = idp

transp-fun : (A B : Set) (a b : A) (p : a == b) (f : A -> B) -> transport (λ _ -> A -> B) p f == transport (λ _ -> B) p (f a)
transp-fun = ?

fe : {A B : Set} (f g : A -> B) -> ( (x : A) -> f x == g x) -> f == g
fe {A} {B} f g p =
  ap
    (I-ind (λ _ → (x : A) → B) f g
      (from-transp (λ _ → (x : A) → B) s ( 
      {!!}
      )))
    s
