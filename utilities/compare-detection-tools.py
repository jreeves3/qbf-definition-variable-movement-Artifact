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
import operator

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

class QBF_Gate_Decoder():
  
  nvar = None
  ncls = None
  
  def __init__(self, qbfName, gateNames,mapNames):
    self.read_qbf(qbfName)
    self.gates = []
    self.gate_maps = []
    self.compare_stats = []
    self.index = 0
    for i in range(len(gateNames)):
      self.gates.append(self.read_gates(gateNames[i]))
      self.index = self.index+1
      self.gate_maps.append(self.read_maps(mapNames[i]))
    
  #####################################################################################
  # PARSING FUNCTIONS
  # QBF, GATES
  #####################################################################################
    
  def read_maps(self,fname):
    mapl = [0] * (self.nvar+1)
    mapt = [-1] * (self.nvar+1)
    file = open(fname, 'r')
    for line in file:
      line = trim(line)
      if len(line) == 0:
        continue
      tokens = line.split()
      orig_v = int(tokens[0])
      new_v = int(tokens[1])
      new_t = int(tokens[2])
      mapl[orig_v] = new_v
      mapt[orig_v] = new_t
    return mapl,mapt
    
  def read_qbf(self, fname):
    file = open(fname, 'r')
    for line in file:
      line = trim(line)
      if len(line) == 0:
        continue
      elif line[0] == 'c':
        continue
      elif line[0] == 'p':
        fields = line[1:].split()
        self.nvar = int(fields[1])
        self.ncls = int(fields[2])
        return

  def read_gates(self, fname):
    file = open(fname, 'r')
    lineNumber = 0
    gatecnt = 0
    g_out = 0
    g_type = 0
    one_sided = True
    one_side_lit = 0
    first = True
    g_clauses = []
    g_inputs = []
    broken_clause = False # Clause not found in input QBF
    xorcnt = 0
    clauses = []
    variable_clauses = {}
    clscnt = 0
    
    gate = {}
    gate['is_gate_out'] = [0] * (self.nvar+1)
    gate['is_xor_out'] = [0] * (self.nvar+1)
    gate['isFound'] = [0] * (self.nvar+1)
    gate['also_monotonic'] = [0] * (self.nvar+1)
    gate['var_gtype'] = {}
    gate['secondary_var_gtype'] = {}
    
    for line in file:
      lineNumber += 1
      line = trim(line)
      if len(line) == 0:
        continue
      elif line[0] == 'c':
        continue
      elif line[0:8] == 'GateType': # Start of new gate
        broken_clause = False
        first = True
        one_sided = True
        fields = line.split()
        g_type = int(fields[1])
        g_out = int(fields[3])
        g_inputs = []
      elif broken_clause: continue # consume lines until next new gate
      elif line[0:4] == 'endG':    # end of a gate
        notFound = False
        g_inputs = list(set(g_inputs))
        
        if g_type == 1 or g_type == 4 or (g_type == 0) or (g_type == 10 and len(g_inputs) <= 2): # eq or xor
          for g_in in g_inputs + [abs(g_out)]:
            gate['is_xor_out'][g_in] = 1
            gate['secondary_var_gtype'][abs(g_in)] = g_type
        else:
          if g_type == 10:
            for g_in in g_inputs + [abs(g_out)]:
              gate['also_monotonic'][g_in] = 1
          else:
            gate['var_gtype'][abs(g_out)] = g_type
            gate['is_gate_out'][abs(g_out)] = 1
        if gate['isFound'][abs(g_out)] == 0: gatecnt += 1
        gate['isFound'][abs(g_out)] = 1
      else: # read in a defining clause for current gate
        lits = [int(s) for s in line.split()]
        if g_type == 0 or g_type == 1 or g_type == 4:
          if abs(lits[-1]) in variable_clauses:
            for clsID in variable_clauses[abs(lits[-1])]:
              cls = clauses[clsID]
              if len(cls) != len(lits): continue
              notS = False
              for l in cls:
                if l not in lits:
                  notS = True
                  break
              if not notS:
                broken_clause = True
                break
            if broken_clause:
              continue
        
          clauses.append(lits)
          vars = [abs(l) for l in lits]
          for v in vars:
              if v in variable_clauses:
                  variable_clauses[v].append(clscnt)
              else:
                  variable_clauses[v] = [clscnt]
          clscnt += 1
        g_inputs += [abs(l) for l in lits]
      
    file.close()
    
    gate['ngates'] = gatecnt
    
    return gate

    
  #####################################################################################
  # GATE DECODING
  #####################################################################################
  
  def compareQBFS(self):
    gate_stats = []
    for i in range(0,len(self.gates)):
      self.compare_stats.append({})
      self.compare_stats[i]["UGates"] = 0
      self.compare_stats[i]["UMoved"] = 0
      gate_stat = {}
      gate_stat['ngate_types'] = [0]*7
      gate_stat['variable_is_moved'] = [0] * (self.nvar + 1)
      gate_stat['new_var'] = {}
      gate_stat['var_gtype'] = {}
      gate_stat['real_movement_cnt'] = 0
      gate_stat['found_cnt'] = 0
      gate_stat['nf'] = 0
      gate_stats.append(gate_stat)
      
    for v in range(1,self.nvar+1):
      isFound = []
      for c in range(0,len(self.gates)):
        if self.gates[c]['isFound'][v] == 1:
          gate_stats[c]['found_cnt'] += 1
          isFound.append(c)
      if len(isFound) == 1:
        self.compare_stats[isFound[0]]["UGates"] += 1
      if len(isFound) > 0 and not 3 in isFound:
        gate_stats[3]['found_cnt'] += 1 # hidden by XOR clauses
              
      # get actual gate value first (if possible)
      g_forced = -1
      kissHas = False
      if self.gates[0]['isFound'][v] == 1:
        kissHas = True
        if self.gates[0]['is_gate_out'][v] == 1 :
          g_forced = self.gates[0]['var_gtype'][v]

      if self.gate_maps[0][0][v] == 1 and g_forced == -1:
        g_forced = self.gate_maps[0][1][v]
      isMoved = []
      if self.gate_maps[3][0][v] == 0: continue # not moved in combined
      for c in range(0,len(self.gates)):
        if self.gate_maps[c][0][v] != 0:
#          mv = self.actual_movement(self.qbfOriginal['variable_qlevel'][v],self.qbfs2[c]['variable_qlevel'][self.gate_maps[c][0][v]],c )
#          if mv > 0:
            isMoved.append(c)
            gate_stats[c]['real_movement_cnt'] += 1
            
            if c==0 and g_forced == 4:
              if not self.gates[1]['also_monotonic'][v] == 1 and not self.gates[1]['is_xor_out'][v] == 1:
                gate_stats[c]['nf'] += 1
              if not self.gates[2]['also_monotonic'][v] == 1 and not self.gates[2]['is_xor_out'][v] == 1:
                gate_stats[2]['nf'] += 1
            if g_forced != -1:
              if g_forced == 10: gate_stats[c]['ngate_types'][6] += 1
              else: gate_stats[c]['ngate_types'][g_forced] += 1
            else:
              g_type = self.gate_maps[c][1][v]
              
              if g_type == 10: gate_stats[c]['ngate_types'][6] += 1
              else: gate_stats[c]['ngate_types'][g_type] += 1
      if len(isMoved) == 1: self.compare_stats[isMoved[0]]["UMoved"] += 1
    self.gate_stats = gate_stats
        
  
#######################################################################################
# MAIN FUNCTION
#######################################################################################
  
def run(name, args):
    formula = None
    
    optlist, args = getopt.getopt(args, "f:")
    for (opt, val) in optlist:
        if opt == '-f':
          formula = val
    f = formula
    formDir = "../formulas/"
    moveDir = "../output/movement/"
    toolDir = "../output/compare-tools/"
    qbfName = formDir+f+".qdimacs"
    gateNames = [moveDir+f+"-cnf-mv.definition",moveDir+f+"-cnf-mb.definition",moveDir+f+"-kissat.definition",moveDir+f+"-comb.definition"]
    mapNames = [toolDir+f+"-cnf-mv-map.txt",toolDir+f+"-cnf-mb-map.txt",toolDir+f+"-kissat-map.txt", moveDir+f+"-map.txt"]

    
    comparison = QBF_Gate_Decoder(qbfName,gateNames,mapNames)
    comparison.compareQBFS()
    
    
    header = ["Tool", "Found", "Moved", "BiEQ Moved","AND/OR Moved", "XOR Moved"]
    line ='%-10s %-20s %-20s %-20s %-20s %-20s' % (header[0],header[1],header[2],header[3],header[4], header[5])
    print("-")
    print(line)
    
    tools = ["cnf-mv", "cnf-mb", "kissat", "combined"]
    for i in range(4):
      line ='%-10s %-20s %-20s %-20s %-20s %-20s' % (tools[i],comparison.gate_stats[i]['found_cnt'], comparison.gate_stats[i]['real_movement_cnt'],comparison.gate_stats[i]['ngate_types'][1],comparison.gate_stats[i]['ngate_types'][2] + comparison.gate_stats[i]['ngate_types'][3],comparison.gate_stats[i]['ngate_types'][4])
      print(line)

    

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
