{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Integers

module Thms where

paths_set : (A B : Set) (m : is-set B) (f g : A -> B) (a : A) -> is-set (f a == g a)
paths_set A B m f g a = \c₁ c₂ q₁ q₂ ->
  prop-has-level-S
    (contr-is-prop (m (f a) (g a) c₁ c₂))
    q₁
    q₂

trunc_paths : (A : Set) (Y : A -> Set) {x y : A} (p : x == y) (t : is-prop (Y x)) (c₁ : Y x) (c₂ : Y y) -> PathOver Y p c₁ c₂
trunc_paths A Y p t c₁ c₂ = from-transp! Y p ((prop-has-all-paths t) c₁ (transport! Y p c₂))

trans-cst : (A : Set) {x y : A} (B : Set) (p : x == y) (z : B) -> transport (\x -> B) p z == z
trans-cst A B idp z = idp

plus : Ints -> Ints -> Ints
plus n = Zind
    (\m -> Ints)
    n
    (\m -> Succ)
    (\m -> Pred)
    (\x y -> from-transp (λ _ → Ints) (invl x) (trans-cst Ints Ints (invl x) (Pred (Succ y)) ∙ invl y))
    (\x y -> from-transp (λ _ → Ints) (invr x) (trans-cst Ints Ints (invr x) (Succ (Pred y)) ∙ invr y))
    (\x -> trunc)

negate : Ints -> Ints
negate = Zind
  (λ _ → Ints)
  nul
  (λ _ -> Pred)
  (λ _ -> Succ)
  (λ x y -> from-transp (λ _ -> Ints) (invl x) (trans-cst Ints Ints (invl x) (Succ (Pred y)) ∙ invr y))
  (λ x y -> from-transp (λ _ -> Ints) (invr x) (trans-cst Ints Ints (invr x) (Pred (Succ y)) ∙ invl y))
  (\x -> trunc)

min : Ints -> Ints -> Ints
min x y = plus x (negate y)

plus_0n : (x : Ints) -> plus x nul == x
plus_0n x = idp

plus_n0 : (x : Ints) -> plus nul x == x
plus_n0 = Zind
  (\x -> plus nul x == x)
  idp
  (\x p -> ap Succ p)
  (\x p -> ap Pred p)
  (\x y ->
    trunc_paths
      Ints
      (\m -> plus nul m == m)
      (invl x)
      (trunc (plus nul (Pred (Succ x)))
      (Pred(Succ x)))
      (ap Pred (ap Succ y))
      y
  )
  (\x y ->
    trunc_paths
      Ints
      (\m -> plus nul m == m)
      (invr x)
      (trunc (plus nul (Succ (Pred x)))
      (Succ(Pred x)))
      (ap Succ (ap Pred y))
      y
  )
  (\x -> paths_set Ints Ints trunc (\m -> plus nul m) (\m -> m) x)

plus_assoc : (x y z : Ints) -> plus x (plus y z) == plus (plus x y) z
plus_assoc x = Zind
  (λ y -> (z : Ints) -> plus x (plus y z) == plus (plus x y) z)
  (
    Zind
      (λ z -> plus x (plus nul z) == plus (plus x nul) z)
      idp
      (λ x p -> ap Succ p)
      (λ x p -> ap Pred p)
      {!!}
      {!!}
      {!!}
  )
  (λ y p ->
    Zind
      (λ z -> plus x (plus (Succ y) z) == plus (plus x (Succ y)) z)
      (p (Succ nul))
      (λ y' p' -> ap Succ p')
      (λ y' p' -> ap Pred p')
      {!!}
      {!!}
      {!!}
  )
  (λ y p ->
    Zind
      (λ z -> plus x (plus (Pred y) z) == plus (plus x (Pred y)) z)
      (p (Pred nul))
      (λ y' p' -> ap Succ p')
      (λ y' p' -> ap Pred p')
      {!!}
      {!!}
      {!!}
  )
  {!!}
  {!!}
  {!!}

plus_Succ : (x y : Ints) -> plus x (Succ y) == Succ(plus x y)
plus_Succ x y = idp

Succ_plus : (x y : Ints) -> plus (Succ x) y == Succ(plus x y)
Succ_plus x = Zind
  (λ y -> plus (Succ x) y == Succ(plus x y))
  idp
  (λ y' p -> ap Succ p)
  (λ y' p -> ap Pred p ∙ invl (plus x y') ∙ ! (invr (plus x y')))
  {!!}
  {!!}
  {!!}

plus_Pred : (x y : Ints) -> plus x (Pred y) == Pred(plus x y)
plus_Pred x y = idp

Pred_plus : (x y : Ints) -> plus (Pred x) y == Pred(plus x y)
Pred_plus x = Zind
  (λ y -> plus (Pred x) y == Pred(plus x y))
  idp
  (λ y' p -> ap Succ p ∙ invr (plus x y') ∙ ! (invl (plus x y')))
  (λ y' p -> ap Pred p)
  {!!}
  {!!}
  {!!}

plus_negr : (y : Ints) -> plus y (negate y) == nul
plus_negr = Zind
  (λ y -> plus y (negate y) == nul)
  idp
  (λ x p ->
    Succ_plus x (negate (Succ x))
    ∙ invr (plus x (negate x))
    ∙ p
  )
  (λ x p ->
    Pred_plus x (negate (Pred x))
    ∙ invl (plus x (negate x))
    ∙ p
  )
  {!!}
  {!!}
  {!!}

plus_negl : (y : Ints) -> plus (negate y) y == nul
plus_negl = Zind
  (λ y -> plus (negate y) y == nul)
  idp
  (λ y' p ->
    Pred_plus (negate y') (Succ y')
    ∙ invl (plus (negate y') y')
    ∙ p
  )
  (λ y' p ->
    Succ_plus (negate y') (Pred y')
    ∙ invr (plus (negate y') y')
    ∙ p
  )
  {!!}
  {!!}
  {!!}

plus_com : (x y : Ints) -> plus x y == plus y x
plus_com x = Zind
  (λ y -> plus x y == plus y x)
  (plus_0n x ∙ ! (plus_n0 x))
  (λ y' p ->
    plus_Succ x y'
    ∙ ap Succ p
    ∙ ! (Succ_plus y' x))
  (λ y' p ->
    plus_Pred x y'
    ∙ ap Pred p
    ∙ ! (Pred_plus y' x)
  )
  {!!}
  {!!}
  {!!}

times : Ints -> Ints -> Ints
times n = Zind
    (λ _ → Ints)
    nul
    (\x y -> plus y n)
    (\x y -> min y n)
    (λ x y -> from-transp (λ _ → Ints) (invl x) (trans-cst Ints Ints (invl x) (min (plus y n) n)
      ∙ ! (plus_assoc y n (negate n))
      ∙ ap (plus y) (plus_negr n)
      ∙ plus_0n y))
    (λ x y -> from-transp (λ _ → Ints) (invr x) (trans-cst Ints Ints (invr x) (plus (min y n) n)
      ∙ ! (plus_assoc y (negate n) n) 
      ∙ ap (λ z -> plus y z) (plus_negl n)
      ∙ plus_0n y))
    (\x -> trunc)
