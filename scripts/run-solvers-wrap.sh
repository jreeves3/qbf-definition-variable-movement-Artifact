#!/bin/bash

mkdir "../output/solvers"

for f in "../formulas/Adder2-8-s.qdimacs" "../formulas/unit11_3_b.qdimacs" "../formulas/nreachq_query71_1344.qdimacs"
do
  echo ""
  echo $(basename "$f" .qdimacs)
  sh run-solvers.sh $f 300 > "../output/solvers/"$(basename "$f" .qdimacs)".log" 2>&1
  python3 ../utilities/printSolvers.py -d ../output/solvers/$(basename "$f" .qdimacs).log -l ../output/movement/move-formulas.log -f $(basename "$f" .qdimacs)
done

