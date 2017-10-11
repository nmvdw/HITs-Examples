# Formalization of Kuratowski-finite sets in homotopy type theory

The Coq docs can be found [here](http://cs.ru.nl/~dfrumin/haan/fsets/)

# Building instructions

Prerequisites: the [HoTT library](https://github.com/HoTT/HoTT).

1. Generate the Makefile: `coq_makefile -f _CoqProject -o Makefile`
2. Compile the library using make: `make -j 2`

An overview of some of the main results can be found in the file `CPP.v`
