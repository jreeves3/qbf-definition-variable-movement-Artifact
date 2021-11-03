#!/bin/bash

for f in "../ldomino-formulas/ldom8.qdimacs" "../ldomino-formulas/ldom18.qdimacs" "../ldomino-formulas/ldom21.qdimacs"
do

  echo $(basename "$f" .qdimacs)

  echo "Detect and Move"
  time sh detect-move.sh $f "../output/ldomino"
#
  python3 ../utilities/mapVariableOrdering.py -m "../output/ldomino/"$(basename "$f" .qdimacs)"-map.txt" -o "../ldomino-formulas/"$(basename "$f" .qdimacs)".order" > "../output/ldomino/"$(basename "$f" .qdimacs)"-move.order"
  
  echo "Run B"
  time python3 ../pgbdd/qbf/qsolver.py -i $f -p "../ldomino-formulas/"$(basename "$f" .qdimacs)".order"
  echo "End Solve"
  
  echo "Moved"
  time python3 ../pgbdd/qbf/qsolver.py -i "../output/ldomino/"$(basename "$f" .qdimacs)"-move.qdimacs" -p "../output/ldomino/"$(basename "$f" .qdimacs)"-move.order"
#
  echo "End Solve"
  echo "Run A"
  
  time python3 ../pgbdd/qbf/qsolver.py -i "../ldomino-formulas/"$(basename "$f" .qdimacs)"-A.qdimacs" -p "../ldomino-formulas/"$(basename "$f" .qdimacs)"-A.order"
  echo "End Solve"
done


