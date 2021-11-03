#!/bin/bash

for f in "../formulas/"*".qdimacs"
do
  echo "Verifying movement for "$(basename "$f" .qdimacs)
  ./../qrat-trim/qrat-trim $f "../output/movement/"$(basename $f .qdimacs)"-move.qrat" -D -v > verification.log
  p=$(grep "all lemmas preserve satisfiability" verification.log | wc | awk '{print  $1}')
  
  if [ $p -gt 0 ]
  then
    echo "Verified"
  else
    echo "Not Verified"
  fi
  rm verification.log
done

