#!/bin/bash
mkdir "../output"
mkdir "../output/movement"

sh move-formulas.sh > "../output/movement/move-formulas.log" 2>&1
