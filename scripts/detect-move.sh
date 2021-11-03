#!/bin/bash

grep -v "^a\|^e" $1 > temp.cnf

echo "DETECT"
timeout 10s ./../cnftools/cnftools temp.cnf -t gates2 > $2"/"$(basename $1 .qdimacs)"-cnf-mb.definition"

timeout 10s ./../cnftools/cnftools temp.cnf -t gates > $2"/"$(basename $1 .qdimacs)"-cnf-mv.definition"

timeout 10s ./../kissat/build/kissat temp.cnf --gateextraction=1 --gatexorrecurse=1

cp kissat_gates.gate $2"/"$(basename $1 .qdimacs)"-kissat.definition"

rm temp.cnf kissat_gates.gate

echo "COMBINE"

python3 ../utilities/combineGates.py -g $2"/"$(basename $1 .qdimacs)"-kissat.definition"  -g $2"/"$(basename $1 .qdimacs)"-cnf-mv.definition"  -g $2"/"$(basename $1 .qdimacs)"-cnf-mb.definition" > $2"/"$(basename $1 .qdimacs)"-comb.definition"


echo "MOVE"

python3 ../qbf-definition-movement.py -q $1 -g $2"/"$(basename $1 .qdimacs)"-comb.definition" -p $2"/"$(basename $1 .qdimacs)"-move.qrat" -o $2"/"$(basename $1 .qdimacs)"-move.qdimacs" -m -b $2"/"$(basename $1 .qdimacs)"-map.txt"

