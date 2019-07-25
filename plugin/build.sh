#!/usr/bin/env bash
git submodule init
git submodule update
echo "building dependencies"
cd deps/fix-to-elim/plugin
./build.sh
cd ../../..
echo "building PUMPKIN PATCH"
coq_makefile -f _CoqProject -o Makefile
make clean && make && make install
