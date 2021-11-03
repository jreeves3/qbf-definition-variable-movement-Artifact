#!/bin/bash
mkdir "../output/bloqqer"

f="k_branch_p-21"
echo $f
./../solvers/bloqqer "../output/movement/"$f"-move.qdimacs" "../output/bloqqer/"$f"-bloqq.qdimacs" --qrat=temp.bloqqer --timeout=100
python3 ../utilities/clean-bloqqer-proof.py -f temp.bloqqer > "../output/bloqqer/"$f"-bloqq.qrat"
rm temp.bloqqer
cat "../output/movement/"$f"-move.qrat" "../output/bloqqer/"$f"-bloqq.qrat" >  "../output/bloqqer/"$f"-full.qrat"
./../qrat-trim/qrat-trim "../formulas/"$f".qdimacs" "../output/bloqqer/"$f"-full.qrat" | tail -n 1

