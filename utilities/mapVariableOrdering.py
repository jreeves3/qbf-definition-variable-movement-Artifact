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

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s
    
def map_ordering(mapfname,varfname):
    variable_map = {}
    mapfile = open(mapfname, 'r')

    lines = [trim(line) for line in mapfile]
    i = 0
    while i < len(lines):
      
      if len(lines[i]) == 0:
        i += 1
        continue
      tokens = lines[i].split()
      variable_map[int(tokens[0])] = int(tokens[1])
      i += 1
        
    varfile = open(varfname, 'r')
    lines = [trim(line) for line in varfile]
    i = 0
    while i < len(lines):
      if len(lines[i]) == 0:
        i += 1
        continue
      tokens = lines[i].split()
      st = ""
      for tk in tokens:
        if int(tk) in variable_map:
          st += " " + str(variable_map[int(tk)])
        else:
          st += " " + tk
#      st = "c o "+ st
      print(st)
      i += 1
    st = ""
    for k in variable_map.keys(): st += " " + str(k)
#    st = "c o "+ st
    print(st)
      
def mapStraight(varfname):
    varfile = open(varfname, 'r')
    lines = [trim(line) for line in varfile]
    i = 0
    while i < len(lines):
      if len(lines[i]) == 0:
        i += 1
        continue
      print("c o "+lines[i])
      i += 1

def run(name, args):
  mapfname = None
  varfname = None
  mapStraightname = False
  optlist, args = getopt.getopt(args, "zm:o:")
  for (opt, val) in optlist:
      if opt == '-m':
        mapfname = val
      elif opt == '-z':
        mapStraightname = True
      elif opt == '-o':
        varfname = val
      
  if mapStraightname:
    mapStraight(varfname)
  else: map_ordering(mapfname,varfname)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
