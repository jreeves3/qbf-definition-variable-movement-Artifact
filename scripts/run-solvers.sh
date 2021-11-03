!/bin/bash
for s in "caqe" "depqbf" "rareqs"
do
  echo "Solver"
  echo $s
  # Run the 4 instances (original, moved, bloqqer, moved-bloqqer)
  echo "Origial"
  time timeout $2 ./"../solvers/"$s $1
  echo "Original End"
  echo "moved"
  time timeout $2 ./"../solvers/"$s "../output/movement/"$(basename $1 .qdimacs)"-move.qdimacs"
  echo "moved End"
  echo "bloqqer"
  time timeout $2 ./"../solvers/"$s "../output/movement/"$(basename $1 .qdimacs)"-bloqq.qdimacs"
  echo "bloqqer End"
  echo "moved-bloqqer"
  time timeout $2 ./"../solvers/"$s "../output/movement/"$(basename $1 .qdimacs)"-move-bloqq.qdimacs"
  echo "moved-bloqqer End"
done
echo "Solver"
echo "ghostq-plain"
echo "Original"


time timeout $2 ./run_ghostq_plain.sh $1
  echo "Original End"

echo "moved"
time timeout $2 ./run_ghostq_plain.sh "../output/movement/"$(basename $1 .qdimacs)"-move.qdimacs"
echo "moved End"
#ex=$?
#echo $ex

echo "bloqqer"
time timeout $2 ./run_ghostq_plain.sh "../output/movement/"$(basename $1 .qdimacs)"-bloqq.qdimacs"
#ex=$?
#echo $ex
echo "bloqqer End"
echo "moved-bloqqer"
time timeout $2 ./run_ghostq_plain.sh "../output/movement/"$(basename $1 .qdimacs)"-move-bloqq.qdimacs"
#ex=$?
#echo $ex
echo "moved-bloqqer End"

echo "Solver"
echo "ghostq-cegar"
echo "Original"

time timeout $2 ./run_ghostq_cegar.sh $1
#ex=$?
#echo $ex
echo "Original End"

echo "moved"
time timeout $2 ./run_ghostq_cegar.sh "../output/movement/"$(basename $1 .qdimacs)"-move.qdimacs"
#ex=$?
#echo $ex
echo "moved End"

echo "bloqqer"
time timeout $2 ./run_ghostq_cegar.sh "../output/movement/"$(basename $1 .qdimacs)"-bloqq.qdimacs"
#ex=$?
#echo $ex
echo "bloqqer End"

echo "moved-bloqqer"
time timeout $2 ./run_ghostq_cegar.sh "../output/movement/"$(basename $1 .qdimacs)"-move-bloqq.qdimacs"
#ex=$?
#echo $ex
echo "moved-bloqqer End"

