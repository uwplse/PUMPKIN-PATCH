#!/bin/sh

OPAM="${HOME}/.opam/$(opam switch show)"

cat >.merlin <<EOF
FLG -rectypes -thread -w @1..50@59-4-44 -safe-string

S src/**
B src/**

PKG threads threads.posix
PKG coq coq.config coq.engine coq.grammar coq.highparsing coq.interp coq.intf coq.kernel coq.lib coq.library coq.ltac coq.parsing coq.pretyping coq.printing coq.proofs coq.stm coq.tactics coq.toplevel coq.vm
S ${OPAM}/build/coq.8.6/**
CMT ${OPAM}/build/coq.8.6/**
EOF
