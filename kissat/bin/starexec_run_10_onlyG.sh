#!/bin/bash

grep -v "^a\|^e" $1 > temp.cnf

echo "DETECT"
timeout 10s ./../build/kissat temp.cnf --gateextraction=1 --gatexorrecurse=1
mv "kissat_gates.gate" $2"/"$(basename $1 .qdimacs)".gate"

