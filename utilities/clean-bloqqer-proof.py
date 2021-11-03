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
    
def read_proof(fname):
    file = open(fname, 'r')
    
    for line in file:
        for i in range(len(line)):
          if line[i:i+3] == " 0 ":
            print(line[0:i+2])
            break
      
def run(name, args):
  fname = None
  optlist, args = getopt.getopt(args, "f:")
  for (opt, val) in optlist:
      if opt == '-f':
        fname = val
        
  read_proof(fname)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
