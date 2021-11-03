This archive provides a demonstration of the tools used in the TACAS 22 submission 
"Moving Definition Variables in Quantified Boolean Formulas".


A. Files and Directories.

The archive contains the following for definition variable movement:

* Kissat - modified for definition extraction, originally found at 
  https://github.com/arminbiere/kissat

* Cnftools - modified for definition extraction, originally found at 
  https://github.com/sat-clique/cnftools

* qbf-definition-movement.py - given a definition file and QBF, moves definition variables 
  generating a QBF in QDIMACS forma and generates a QRAT proof for verifying the movement


The archive contains the following for evaluating definition variable movement:

* qrat-trim - modified to verify QRAT proofs for definition variable movement, originally found at 
  https://github.com/marijnheule/qrat-trim

* solvers - binaries of the 4 QBF solvers used in the paper, found at:  
  https://github.com/ltentrup/caqe (Caqe)
  https://github.com/lonsing/depqbf (DepQBF)
  http://sat.inesc-id.pt/~mikolas/sw/areqs/ (RareQS)
  https://www.wklieber.com/ghostq/ (GhostQ and qcir-conv.py)
  http://fmv.jku.at/bloqqer/ (bloqqer preprocessor)

* pgbddq - BDD-based QBF solver, originally found at 
  https://github.com/rebryant/pgbdd

* scripts - shell scripts for running the definition variable movement and evaluating the movement

* utilities - additional python programs for output and file mapping used in the scripts 

* formulas - a selection of formulas from QBFEVAL'20 http://www.qbflib.org/qbfeval20.php

* ldomino-formulas - a selection of ldomino formulas, created from the generator in pgbddq


B. Build.

Run the following command:

	> sh build.sh

This will build the dependencies in the directory packages (python2 and libarchive-dev) that are 
not in the TACAS 2022 virtual machine, then build the tools Kissat, Cnftools, and qrat-trim.


C. Scripts.

* Logs for all evaluation scripts run on the TACAS22 vm can be found in the directory script-logs.


First navigate to the scripts directory,

	> cd scripts

* Note script (1) must be run before any of 1.(a,b,c,d).

1. Detect and Move formulas (Approx. 2m) 

		> sh move-formulas-wrap.sh

	Makes the output directory.
	
	Calls detect-move.sh on the 7 formulas in the formulas directory:

		This runs the 3 definition detection tools each for 10 seconds, 
		generating definition files definition files "output/movement/<formula>-<tool>.definition".
		The definitions are combined into a single file "output/movement/<formula>-comb.definition"

		Then this runs qbf-definition-movement.py to move definitions.
		This generates new qbf "output/movement/<formula>-move.qdimacs", a qrat proof
		"output/movement/<formula>-move.qrat", and a map "output/movement/<formula>-map.txt".
		The map contains a list of triples (original variable, new variable, definition type)

	Calls bloqqer with a 100 second timeout on the formulas 
	Adder2-8-s, unit11_3_b.qdimacs, nreachq_query71_1344.qdimacs generating the files
	"output/movement/<formula>-bloqq.qdimacs".
	Also calls bloqqer on the moved version of these formulas, generating the files
	"output/movement/<formula>-move-bloqq.qdimacs".

1.a Compare Definition Detection Tools (Table 1,2 and Figure 1) (Approx. 30s)
	
		> sh compare-detection-tools.sh

	This runs qbf-definition-movement.py to move definitions using the definitions extracted
	from each of the three tools kissat, cnf-mv (max-variable), and cnf-mb (min-blocked).
	The output files are stored in "output/compare-tools".

	The output is compared for each of the 7 formulas, printing tables that collectively show a
	subset of the data used in Table 1 and Table 2.


1.b Verify Movement (Section 4.3) (Approx. 5m)
	
		> sh verify-movement.sh

	Calls qrat-trim to check the proofs generated during movement for the 7 formulas.

	The output prints "s Verified" for formulas that have been correctly verified.


1.c Verify Full Proof with Bloqqer (Section 4.3) (Approx. 2m)

		> sh bloqq-end2end.sh

	Calls bloqqer on the moved formula for "output/movement/k_branch_p-21-move.qdimacs",
	solving the formula and emitting QRAT a proof stored in "output/bloqqer"
	This QRAT proof is appended to the QRAT proof of movement, and the combined proof is checked on 
	the original formula k_branch_p-21 using qrat-trim.

	This outputs the last line produced by the call to qrat-trim "s VERIFIED".

1.d Run solvers (Figure 2,3) (Approx. 3h)
	
		> sh run-solvers-wrap.sh

	Runs the five QBF solver configurations on the original, moved, bloqqed, and moved-bloqqed
	instances of the formulas Adder2-8-s, unit11_3_b.qdimacs, nreachq_query71_1344.qdimacs.
	Solver operate with a 300 second timeout (5000 seconds were used in the paper). Logs
	are stored in the directory "output/solvers"

	Tables are printed for each formula showing the results, with -1 denoting a timeout.
	The solve times for moved formulas include movement time, and the solve times for formulas
	preprocessed with bloqqer include the bloqqer time.

2. Ldomino and pgbddq (Figure 4) (Approx. 35m)

	> sh ldomino-wrap.py

	Moves definition variables for the 3 ldomino formulas N={8,18,21}. Files are stored in the
	directory "output/ldomino".
	Runs pgbddq on the 3 definition variable placement schemes End, Moved, and After (formulas with 
	-A in the name). 

	A table is printed with -1 denoting memory out.


D. Data

The data directory contains excel spreadsheets for data used in the Tables and Figures of the paper.
For Figure2,3,4 data, a time of 5000s denotes a timeout.

The data for the submitted paper did not capture the entire QBFEVAL'20 benchmark suite:
2 formulas (of the 494) were not included in the data in Table 1 of the paper, 
and approximately 20 (of the 494) formulas were not included in the data for Figures1,2,3 and Table 3. 
This was due to an accidental defect in the data-extraction scripts.

The updated Figures and Tables containing the full dataset are reflected in the pdf 
"qbf-definition-extraction.pdf". The new figures do not change the observations or conclusions drawn 
in the the submitted paper.
