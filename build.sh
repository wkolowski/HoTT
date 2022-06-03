#!/bin/sh

coq_makefile -R "." HoTT -arg "-async-proofs-cache force -noinit" -o makefile $(find . -name "*v")

make -j `nproc`

rm makefile makefile.conf .makefile.d
