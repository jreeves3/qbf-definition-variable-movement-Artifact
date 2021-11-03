#!/bin/bash

for f in "../formulas/"*".qdimacs"
do
  echo $(basename "$f" .qdimacs)
  echo "Detect and Move"
  time sh detect-move.sh $f "../output/movement"
  echo "Finish Move"
done

for f in "../formulas/Adder2-8-s.qdimacs" "../formulas/unit11_3_b.qdimacs" "../formulas/nreachq_query71_1344.qdimacs"
do
  echo $(basename "$f" .qdimacs)
  echo "Bloqqer on Original Formula"
  time ./../solvers/bloqqer $f "../output/movement/"$(basename "$f" .qdimacs)"-bloqq.qdimacs" --timeout=100
  echo "Finish Bloqqer on Original Formula"
  echo "Bloqqer on Moved Formula"
  time ./../solvers/bloqqer "../output/movement/"$(basename "$f" .qdimacs)"-move.qdimacs" "../output/movement/"$(basename "$f" .qdimacs)"-move-bloqq.qdimacs" --timeout=100
  echo "Finish Bloqqer on Moved Formula"
done
