{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module CL where

private
  data CL' : Set where
    K' : CL'
    S' : CL'
    app' : CL' -> CL' -> CL'

CL : Set
CL = CL'

K : CL
K = K'

Sc : CL
Sc = S'

app : CL -> CL -> CL
app = app'

postulate
  KConv : {x y : CL} -> app (app K x) y == x
  SConv : {x y z : CL} -> app (app (app Sc x) y) z == app (app x z) (app y z)

CLind : (Y : CL -> Set)
        (KY : Y K)
        (SY : Y Sc)
        (appY : (x y : CL) -> Y x -> Y y -> Y (app x y))
        (KConvY : (x y : CL) (a : Y x) (b : Y y) -> PathOver Y KConv (appY (app K x) y (appY K x KY a) b) a)
        (SConvY : (x y z : CL) (a : Y x) (b : Y y) (c : Y z) ->
          PathOver Y SConv
            (appY
              (app (app Sc x) y)
              z
              (appY
                (app Sc x)
                y
                (appY Sc x SY a)
                b
              )
              c
            )
            (appY (app x z) (app y z) (appY x z a c) (appY y z b c))
        )
        (x : CL) -> Y x
CLind Y KY SY appY _ _ K' = KY
CLind Y KY SY appY _ _ S' = SY
CLind Y KY SY appY KConvY SConvY (app' x x₁) = appY x x₁ (CLind Y KY SY appY KConvY SConvY x) (CLind Y KY SY appY KConvY SConvY x₁)

postulate
  CLind_βKConv : (Y : CL -> Set)
        (KY : Y K)
        (SY : Y Sc)
        (appY : (x y : CL) -> Y x -> Y y -> Y (app x y))
        (KConvY : (x y : CL) (a : Y x) (b : Y y) -> PathOver Y KConv (appY (app K x) y (appY K x KY a) b) a)
        (SConvY : (x y z : CL) (a : Y x) (b : Y y) (c : Y z) ->
          PathOver Y SConv
            (appY
              (app (app Sc x) y)
              z
              (appY
                (app Sc x)
                y
                (appY Sc x SY a)
                b
              )
              c
            )
            (appY (app x z) (app y z) (appY x z a c) (appY y z b c))
        )
        (x y : CL) ->
        apd (CLind Y KY SY appY KConvY SConvY) KConv == KConvY x y (CLind Y KY SY appY KConvY SConvY x) (CLind Y KY SY appY KConvY SConvY y)
  CLind_βSConv : (Y : CL -> Set)
        (KY : Y K)
        (SY : Y Sc)
        (appY : (x y : CL) -> Y x -> Y y -> Y (app x y))
        (KConvY : (x y : CL) (a : Y x) (b : Y y) -> PathOver Y KConv (appY (app K x) y (appY K x KY a) b) a)
        (SConvY : (x y z : CL) (a : Y x) (b : Y y) (c : Y z) ->
          PathOver Y SConv
            (appY
              (app (app Sc x) y)
              z
              (appY
                (app Sc x)
                y
                (appY Sc x SY a)
                b
              )
              c
            )
            (appY (app x z) (app y z) (appY x z a c) (appY y z b c))
        )
        (x y z : CL) ->
        apd (CLind Y KY SY appY KConvY SConvY) SConv == SConvY x y z (CLind Y KY SY appY KConvY SConvY x) (CLind Y KY SY appY KConvY SConvY y) (CLind Y KY SY appY KConvY SConvY z)
