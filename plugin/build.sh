#!/usr/bin/env bash
git submodule init
git submodule update
echo "building PUMPKIN PATCH dependencies"
cd deps/fix-to-elim/plugin
./build.sh
cd ../../..
cd deps/ornamental-search/plugin
./build.sh
cd ../../..
echo "done building PUMPKIN PATCH dependencies"
echo "building PUMPKIN PATCH"
coq_makefile -f _CoqProject -o Makefile
make clean && make && make install
