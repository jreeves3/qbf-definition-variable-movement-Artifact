#####################################################################################
# Copyright (c) 2021 Joseph Reeves, Marijn Heule, Randal E. Bryant, Carnegie Mellon University
# Last edit: Nov. 2, 2021
#
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################

import sys
import getopt
import functools

  
def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s
    
def get_result(solver, line):
  verif_line = line.split()
  if len(verif_line) == 0: return False
  if solver == 'caqe' and (len(verif_line) > 1) and (verif_line[1] == 'Satisfiable' or verif_line[1] == 'Unsatisfiable'):
    return True
  elif (solver == "ghostq-plain" or solver == "ghostq-cegar") and (verif_line[0][0] == "s"):
    return True
  elif solver == "depqbf" and (verif_line[0] == "SAT" or verif_line[0] == "UNSAT"):
    return True
  elif solver == "rareqs" and (verif_line[0][0] == "s"):
    return True
  else: return False

def get_time(line):
  tokens = line.split()
  time = float(tokens[0][:-4]) # user time
  return time
 
def get_solve_times(solveFile):
  file = open(solveFile, 'r')
  solve_dic = {}
  solver = None
  start = 0
  lines = [line for line in file]
  for i in range(len(lines)):
    line = lines[i]
    line = trim(line)
    if line == "Solver":
      solver= trim(lines[i+1])
      solve_dic[solver] = []
    elif line in ["Original", "moved", "bloqqer", "moved-bloqqer"]:
      start = i
    elif line in ["Original End", "moved End", "bloqqer End", "moved-bloqqer End"]:
      time = get_time(lines[i-2])
      result = get_result(solver, lines[i-4])
      if not result: time = -1
      solve_dic[solver].append(time)
    i += 1
    
  return solve_dic
 
def get_move_times(moveFile):
  file = open(moveFile, 'r')
  move_dic = {}
  lines = [line for line in file]
  for i in range(len(lines)):
    line = lines[i]
    line = trim(line)
    if line == "Detect and Move":
      bench = trim(lines[i-1])
    elif line == "Bloqqer on Original Formula":
      bench = trim(lines[i-1])
#    elif line == "Bloqqer on Moved Formula":
#      bench = lines[i-1]
    elif line == "Finish Move":
      move_dic[bench] = [get_time(lines[i-2])]
    elif line == "Finish Bloqqer on Original Formula":
      move_dic[bench].append(get_time(lines[i-2]))
    elif line == "Finish Bloqqer on Moved Formula":
      move_dic[bench].append(get_time(lines[i-2]))
    i += 1
    
  return move_dic
  
 
def extract(formula, solveFile, moveFile):
  move_dic = get_move_times(moveFile)
#  print(move_dic)
  solve_dic = get_solve_times(solveFile)
#  print(solve_dic)
  header = ["Solver", "Original", "Moved", "Bloqqer","Moved-Bloqqer"]
  line ='%-15s %-20s %-20s %-20s %-20s' % (header[0],header[1],header[2],header[3],header[4])
  print("-")
  print(line)
  
  solvers = ["caqe", "depqbf", "rareqs", "ghostq-plain", "ghostq-cegar"]
  for i in range(5):
    valsT = [solve_dic[solvers[i]][0], (solve_dic[solvers[i]][1]+move_dic[formula][0]), (solve_dic[solvers[i]][2]+move_dic[formula][1]),  (solve_dic[solvers[i]][3]+move_dic[formula][0]+move_dic[formula][2])]
    
    for j in range(4):
      if solve_dic[solvers[i]][j] == -1: valsT[j] = -1
    
    line ='%-15s %-20s %-20s %-20s %-20s' % (solvers[i],"%.2f" % valsT[0], "%.2f" %  valsT[1], "%.2f" %  valsT[2], "%.2f" %  valsT[3])
    print(line)
  
    
    
#######################################################################################
# MAIN FUNCTION
#######################################################################################
  
def run(name, args):
    
    moveFile = None
    solveFile = None
    formula = None

    optlist, args = getopt.getopt(args, "l:d:f:")
    for (opt, val) in optlist:
      if opt == '-f':
          formula = val
      elif opt == '-d':
        solveFile = val
      elif opt == '-l':
        moveFile = val
    extract(formula, solveFile, moveFile)
        

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
