#!/bin/sh

coq_makefile -R "." HoTT -arg "-async-proofs-cache force -noinit" -o makefile $(find . -name "*v")
make
rm makefile makefile.conf .makefile.d
