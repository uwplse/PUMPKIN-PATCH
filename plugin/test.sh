#!/usr/bin/env bash
coqc coq/Regress.v
coqc coq/Variants.v > ~/foo.txt
coqc coq/Abstract.v
coqc coq/divide.v
coqc coq/Induction.v
coqc coq/IntegersNew.v
coqc coq/Optimization.v
