#!/bin/sh

coqc coq/Decompiler.v > coq/decompile.out
diff coq/decompile.out coq/decomp_regress.txt
