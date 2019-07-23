#!/usr/bin/env bash
git submodule init
git submodule update
coq_makefile -f _CoqProject -o Makefile
make clean && make && make install
