# HITs-Coq

Needed: https://github.com/HoTT/HoTT

More information on the work is in HITs.pdf.

# Building

Make sure that you have [hoqc](https://github.com/HoTT/HoTT) installed. Then generate
the Makefile and build the project:

    coq_makefile -f _CoqProject -o Makefile
    make