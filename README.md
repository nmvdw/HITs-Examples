# HITs-Coq

Needed: https://github.com/HoTT/HoTT

The Finite Sets library of the 'Finite Sets in Homotopy Type Theory' is in the directory 'Finite Sets'.

The only part of the project that is buildable is the `FiniteSets` library.

# Building

Before proceeding make sure that you have [hoqc](https://github.com/HoTT/HoTT) installed.

1. Build the `HitTactics` library in `prelude`.
```
cd prelude
hoqc HitTactics
```
2. Generate the Makefile and build the `FiniteSets` library
```
cd ../FiniteSets
coq_makefile -f _CoqProject -o Makefile
make
```    
