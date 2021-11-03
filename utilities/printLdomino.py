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
  return ("SAT" in line)

def get_time(line):
  tokens = line.split()
  time = float(tokens[0][:-4]) # user time

  return time
 
def get_solve_times(moveFile):
  file = open(moveFile, 'r')
  solve_dic = {}
  solve_dic["E"] = []
  solve_dic["M"] = []
  solve_dic["A"] = []
  solver = None
  start = 0
  lines = [line for line in file]
  for i in range(len(lines)):
    line = lines[i]
    line = trim(line)
    if line == "Run B":
      solver="E"
    elif line == "Moved":
      solver="M"
    elif line == "Run A":
      solver="A"
    elif line == "End Solve":
      time = get_time(lines[i-2])
      result = get_result(solver, lines[i-3])
      if not result: time = -1
      solve_dic[solver].append(time)
    i += 1
    
  return solve_dic
 
def get_move_times(moveFile):
  file = open(moveFile, 'r')
  move_dic =[]
  lines = [line for line in file]
  for i in range(len(lines)):
    line = lines[i]
    line = trim(line)
    if line == "MOVE":
      move_dic.append(get_time(lines[i+2]))
    i += 1
    
  return move_dic
  
 
def extract(moveFile):
  move_dic = get_move_times(moveFile)
#  print(move_dic)
  solve_dic = get_solve_times(moveFile)
#  print(solve_dic)
  header = ["N", "Variable Placement", "End", "Moved", "After"]
  line ='%-5s %-20s %-20s %-20s %-20s' % (header[0],header[1],header[2],header[3],header[4])
  print("-")
  print(line)
  ns = [8,18,21]
  for i in range(3):
    line ='%-5s %-20s %-20s %-20s %-20s' % (ns[i],"","%.2f" % solve_dic["E"][i], "%.2f" %  (solve_dic["M"][i]+move_dic[i]), "%.2f" % solve_dic["A"][i])
    print(line)
  
    
    
#######################################################################################
# MAIN FUNCTION
#######################################################################################
  
def run(name, args):
    
    moveFile = None

    optlist, args = getopt.getopt(args, "l:")
    for (opt, val) in optlist:
      if opt == '-l':
        moveFile = val
    extract(moveFile)
        

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
