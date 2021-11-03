#!/bin/bash

grep -v "^a\|^e" $1 > temp.cnf

echo "DETECT"
timeout 10s ./../build/kissat temp.cnf --gateextraction=1 --gatexorrecurse=1
mv "kissat_gates.gate" $2"/"$(basename $1 .qdimacs)".gate"

echo "MOVE"
python3 ../qbf-gate-processor.py -q $1 -g $2"/"$(basename $1 .qdimacs)".gate" -p temp.qrat -o $2"/"$(basename $1 .qdimacs)".qdimacs" -m -b $2"/"$(basename $1 .qdimacs)"map.txt"

echo "QRAT"
./../qrat-trim/qrat-trim $1 temp.qrat -D -v > temp.qout

p=$(grep "all lemmas preserve satisfiability" temp.qout | wc | awk '{print  $1}')
  
  if [ $p -gt 0 ]
  then
    echo "v Verified C\n"
  else
    echo "v Not Verified C\n"
  fi
