#!/bin/bash

mkdir "../output/ldomino"

sh ldomino.sh > "../output/ldomino/ldomino.log" 2>&1

python3 ../utilities/printLdomino.py -l "../output/ldomino/ldomino.log"


