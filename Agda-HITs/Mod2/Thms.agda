{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Mod2

module Thms where

paths_set : (A B : Set) (m : is-set B) (f g : A -> B) (a : A) -> is-set (f a == g a)
paths_set A B m f g a = \c₁ c₂ q₁ q₂ ->
  prop-has-level-S
    (contr-is-prop (m (f a) (g a) c₁ c₂))
    q₁
    q₂

trunc_paths : (A : Set) (Y : A -> Set) {x y : A} (p : x == y) (t : is-prop (Y x)) (c₁ : Y x) (c₂ : Y y) -> PathOver Y p c₁ c₂
trunc_paths A Y p t c₁ c₂ = from-transp! Y p ((prop-has-all-paths t) c₁ (transport! Y p c₂))

plus : M -> M -> M
plus n = M-rec
  n
  Succ
  mod
  trunc

plus_0n : (n : M) -> plus z n == n
plus_0n = M-ind
  (\n -> plus z n == n)
  idp
  (\x -> \p -> ap Succ p)
  (\x -> \c ->
    trunc_paths M (\ n → plus z n == n) (mod x) (trunc (plus z x) x) c (ap Succ (ap Succ c))
  )
  (\m ->
    paths_set M M trunc (\x -> plus z x) (\x -> x) m
  )

plus_n0 : (n : M) -> plus n z == n
plus_n0 = M-ind
  (\n -> plus n z == n)
  idp
  (\x p -> idp)
  (\x c ->
    trunc_paths M (\x -> plus x z == x) (mod x) (trunc x x) c idp
  )
  (\m -> paths_set M M trunc (\x -> plus x z) (\x -> x) m )

plus_Sn : (n m : M) -> plus (Succ n) m == Succ (plus n m)
plus_Sn n = M-ind
  (\m -> plus (Succ n) m == Succ (plus n m))
  idp
  (\x p -> ap Succ p)
  (\x c ->
    trunc_paths M (\x -> plus (Succ n) x == Succ (plus n x)) (mod x) (trunc (plus (Succ n) x) (Succ (plus n x))) c (ap Succ (ap Succ c))
  )
  (\m -> paths_set M M trunc (\x -> plus (Succ x) m) (\x -> Succ(plus x m)) n)

plus_nS : (n m : M) -> plus n (Succ m) == Succ (plus n m)
plus_nS n m = idp

not : Bool -> Bool
not true = false
not false = true

not-not : (x : Bool) -> x == not (not x)
not-not true = idp
not-not false = idp

toBool : M -> Bool
toBool = M-rec
  true
  not
  ((\x -> not-not x))
  Bool-is-set

toBoolS : (n : M) -> toBool (Succ n) == not (toBool n)
toBoolS = M-ind
  (\n -> toBool (Succ n) == not (toBool n))
  idp
  (\x p -> idp)
  (\n c ->
    trunc_paths M (\x -> toBool (Succ x) == not (toBool x)) (mod n) (Bool-is-set (not (toBool n)) (not (toBool n))) c idp)
  (\m -> paths_set M Bool Bool-is-set (\n -> toBool(Succ n)) (\n -> not(toBool n)) m)

fromBool : Bool -> M
fromBool true = z
fromBool false = Succ z

fromBoolNot : (b : Bool) -> fromBool (not b) == Succ (fromBool b)
fromBoolNot true = idp
fromBoolNot false = mod z

iso₁ : (b : Bool) -> toBool (fromBool b) == b
iso₁ true = idp
iso₁ false = idp

iso₂ : (n : M) -> fromBool (toBool n) == n
iso₂ = M-ind
  (\n -> fromBool (toBool n) == n)
  idp
  (\x p ->
    ap fromBool (toBoolS x)
    ∙ fromBoolNot (toBool x)
    ∙ ap Succ p)
  (\n p -> trunc_paths M
    (λ z₁ → fromBool (toBool z₁) == z₁)
    (mod n)
    (trunc (fromBool (toBool n)) n)
    p
    (ap fromBool (toBoolS (Succ n))
      ∙ fromBoolNot (toBool (Succ n))
      ∙ ap Succ (ap fromBool (toBoolS n) ∙ fromBoolNot (toBool n) ∙ ap Succ p))
  )
  (\m -> paths_set M M trunc (\n -> fromBool (toBool n)) (\n -> n) m)
