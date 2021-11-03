#!/bin/bash

mkdir "../output/compare-tools"

defDir="../output/movement"
outDir="../output/compare-tools"

for f in "../formulas/"*".qdimacs"
do

  echo $(basename $f .qdimacs)

  python3 ../qbf-definition-movement.py -q $f -g $defDir"/"$(basename $f .qdimacs)"-cnf-mv.definition" -p /dev/null -o /dev/null -m -b $outDir"/"$(basename $f .qdimacs)"-cnf-mv-map.txt" -t "cnf-mv"
  
  python3 ../qbf-definition-movement.py -q $f -g $defDir"/"$(basename $f .qdimacs)"-cnf-mb.definition" -p /dev/null -o /dev/null -m -b $outDir"/"$(basename $f .qdimacs)"-cnf-mb-map.txt" -t "cnf-mb"
    
  python3 ../qbf-definition-movement.py -q $f -g $defDir"/"$(basename $f .qdimacs)"-kissat.definition" -p /dev/null -o /dev/null -m -b $outDir"/"$(basename $f .qdimacs)"-kissat-map.txt" -t "kissat"
  
  python3 ../utilities/compare-detection-tools.py -f $(basename $f .qdimacs)
  
done
