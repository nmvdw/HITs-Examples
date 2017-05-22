{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import CL

module Thms where

trans-cst : (A : Set) {x y : A} (B : Set) (p : x == y) (z : B) -> transport (\x -> B) p z == z
trans-cst A B idp z = idp

I : CL
I = app (app Sc K) K

IConv : {x : CL} -> app I x == x
IConv {x} = SConv ∙ KConv

B : CL
B = app (app Sc (app K Sc)) K

BConv : {x y z : CL} -> app (app (app B x) y) z == app x (app y z)
BConv {x} {y} {z} =
  ap (λ p -> app (app p y) z) SConv
  ∙ ap (λ p -> app (app (app (p) (app K x)) y) z) KConv
  ∙ SConv
  ∙ ap (λ p -> app p (app y z)) KConv

M : CL
M = app (app Sc I) I

MConv : {x : CL} -> app M x == app x x
MConv {x} =
  SConv
  ∙ ap (λ p -> app p (app I x)) IConv
  ∙ ap (app x) IConv

T : CL
T = app (app B (app Sc I)) K

TConv : {x y : CL} -> app (app T x) y == app y x
TConv {x} {y} =
  ap (λ p -> app p y) BConv
  ∙ SConv
  ∙ ap (λ p -> app p (app (app K x) y)) IConv
  ∙ ap (app y) KConv

C : CL
C =
  app
    (app
      B
      (app
        T
        (app
          (app
            B
            B
          )
        T
        )
      )
    )
    (app
      (app
        B
        B
      )
      T
    )

CConv : {x y z : CL} -> app (app (app C x) y) z == app (app x z) y
CConv {x} {y} {z} =
  ap (λ p -> app (app p y) z) BConv
  ∙ ap (λ p -> app (app p y) z) TConv
  ∙ ap (λ p -> app (app (app p (app (app B B) T)) y) z) BConv
  ∙ ap (λ p -> app p z) BConv
  ∙ ap (λ p -> app p z) TConv
  ∙ ap (λ p -> app (app p x) z) BConv
  ∙ BConv
  ∙ TConv

W : CL
W = app (app C Sc) I

WConv : {x y : CL} -> app (app W x) y == app (app x y) y
WConv {x} {y} =
  ap (λ p -> app p y) CConv
  ∙ SConv
  ∙ ap (app (app x y)) IConv

B' : CL
B' = app C B

B'Conv : {x y z : CL} -> app (app (app B' x) y) z == app y (app x z)
B'Conv {x} {y} {z} =
  ap (λ p -> app p z) CConv
  ∙ BConv

V : CL
V = app (app B C) T

VConv : {x y z : CL} -> app (app (app V x) y) z == app (app z x) y
VConv {x} {y} {z} =
  ap (λ p -> app (app p y) z) BConv
  ∙ CConv
  ∙ ap (λ p -> app p y) TConv

Y : CL
Y = app (app B' (app B' M)) M

YConv : {x : CL} -> app Y x == app x (app Y x)
YConv {x} =
  B'Conv
  ∙ MConv
  ∙ B'Conv
  ∙ ap (app x) (! B'Conv)

fixpoint : (x : CL) -> Σ CL (λ y -> app x y == y)
fixpoint x = app Y x , ! YConv

S' : CL
S' = app C Sc

