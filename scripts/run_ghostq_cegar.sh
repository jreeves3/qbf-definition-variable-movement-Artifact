#!/bin/bash
# USAGE: ./solver.sh INPUTFILE

python2 ../solvers/qcir-conv.py $1 --quiet -write-gq | ./../solvers/ghostq - -s-cnf -q2 -cegar 1 

