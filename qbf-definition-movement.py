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
from queue import Queue

def usage(name):
    sys.stderr.write("Usage: %s [-h] [-m]  [-v LEVEL] [-q PCNF] [-g DEFINITION] [-o OUTPCNF] [-o OUTMAP] " % name)
    sys.stderr.write("  -h                Print this message\n")
    sys.stderr.write("  -v LEVEL          Verbose output level 1: definition detection...\n")
    sys.stderr.write("  -q PCNF           Name of PCNF input file\n")
    sys.stderr.write("  -g DEFINITION     Name of DEFINITION input file\n")
    sys.stderr.write("  -o OUTPCNF        Name of Output PCNF file\n")
    sys.stderr.write("  -b OUTMAP         Name of Output map file: (var, newvar, type)\n")
    sys.stderr.write("  -m                Move definitions in output PCNF\n")


def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

class QbfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "QBF Exception: " + str(self.value)
        
class DefinitionException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Definition Exception: " + str(self.value)


class Definition():
  
  def __init__(self, d_outlit, d_clauses, d_inputs, d_type):
    self.outlit   = d_outlit
    self.clauses  = d_clauses
    self.inputs   = d_inputs
    self.type     = d_type

class QBF_Definition_Processor():
  
  verbosity = 0         # level of verbose output
  
  # QBF information
  nvar = 0
  nvar_orig = 0
  ncls = 0
  nqlevels = 0
  variable_clauses = {} # map: vid -> list of clsids
  variable_qlevel  = {} # map: vid -> qlevel (quantification level) id
  clauses = []          # list of clauses, clause is list of integers
  quantifiers = []      # list of pairs ("a|e", [vids])
  
  # Definition information
  ndefinitions = 0
  definitions = []            # list of definitions
  is_definition_out    = []   # vid -> 1 if vid is output of a definition, 0 otherwise
  variable_d_out = {}   # map: vid -> definition that vid is the output of
  variable_g_in  = {}   # map: vid -> definitions that vid is the input of
  
  # XOR definition information
  nxor_definitions = 0
  xor_definitions = []          # list of xor definitions (d_out, d_clauses, d_inputs)
                          #   d_out is the temporary definition output giving by the definition
                          #   definition. This may change in xor definition processing
  variable_xor_definitions = {} # map: vid   -> xor definition ids with vid in defining clauses
  clauses_xor_definitions  = {} # map: clsid -> xor definition id with clsid in definition
  
  # Definition processing information
  ndefinitions_moved = 0      # number of definition outputs moved to lower qlevel
                        # variables in defining clauses (not proper definitions in qbf)
  total_nlevels_moved=0 # sum of diff in level for each variable moved
  var_map = [0]         # map old variable IDs to new values (when introducing
                        # new Tseiten variables
  reverse_var_map = [0]
  actual_move_type = {}
  restrictDefinitions = False
  
  one_sided_moves                 = 0
  definitions_out_of_order        = 0
  definitions_on_universal        = 0
  definitions_notdefined          = 0
  definitions_one_sided_incorrect = 0
  nxor_moved                      = 0
  nsemantic_moved                 = 0
  
  last_level = []       # LDomino check on movement of variables in last Qlevel
  var_moved = None
  
  candidate_lists = None # move algorithm
  seen_n = None
  seen_xor = None
  
  proof = None
  writeProof = False
  prove_no_write = False

  def __init__(self, qbfName, proofName = None, verbosity = 0, prove_no_write = False, restrictDefinitions = False, pseudo = False, tool = None):
    if not proofName is None:
      self.proof = open(proofName, 'w')
      self.writeProof = True
    self.prove_no_write = prove_no_write
    self.restrictDefinitions = restrictDefinitions
    self.pseudo = pseudo
    self.tool = tool

    self.read_qbf(qbfName)
    for i in range(1,self.nvar+1):
      self.var_map.append(i)
      self.reverse_var_map.append(i)
    self.verbosity = verbosity
    
    for i in self.quantifiers[-2][1]: # variables in last level
      self.last_level.append(i)
    self.var_moved = [0]*(self.nvar+1)
    self.nvar_orig = self.nvar
    
    
    
  #####################################################################################
  # PARSING FUNCTIONS
  # QBF, DEFINITIONS
  #####################################################################################

    
  # Parser adapted from PGBDDQ, Randy E. Bryant
  # Read quantifiers and clauses into QBF information
  # Quantifier levels (qlevels) are read as even numbers 0,2,4,..
  #   odd numbered qlevels reserved for moved T-Levels
  def read_qbf(self, fname):
    file = open(fname, 'r')
    lineNumber = 0
    qlevel = 0
    clscnt = 0
    getting_quantifiers = False
    
    for line in file:
      lineNumber += 1
      line = trim(line)
      if len(line) == 0:
        continue
      elif line[0] == 'c':
        continue
      elif line[0] == 'p':
        fields = line[1:].split()
        if len(fields) != 3 or fields[0] != 'cnf':
            raise QbfException("Line %d.  Bad header line '%s'.  Not qbf" % (lineNumber, line))
        try:
          self.nvar = int(fields[1])
          self.ncls = int(fields[2])
        except Exception:
          raise QbfException("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
        self.is_definition_out = [0] * (self.nvar +1)
        getting_quantifiers = True
        
      elif line[0] == 'a' or line[0] == 'e':
        if not getting_quantifiers:
          raise QbfException("Line %d.  Quantifier out of order line '%s'.  Not qbf" % (lineNumber, line))
        try:
            vars = [int(s) for s in line[1:].split()]
        except:
            raise QbfException("Line %d.  Non-integer field" % lineNumber)
        if vars[-1] != 0:
            raise QbfException("Line %d.  Quantifier line should end with 0" % lineNumber)
        vars = vars[:-1]
        self.quantifiers.append((line[0],vars[:])) # Original quantifier level (Even index 0,2,4,...)
        self.quantifiers.append(('e',[])) # T-level following original quantifier level (Odd index 1,3,5,...)
        for v in vars: # check variable not in a previous qlevel
          if v in self.variable_qlevel:
            raise QbfException("Line %d.  %d in two quantifier levels.  Not qbf" % (lineNumber, v))
          self.variable_qlevel[v] = qlevel
        qlevel += 2 # reserve odds for T-Level
      else:
        getting_quantifiers = False
        # Check formatting
        try:
          lits = [int(s) for s in line.split()]
        except:
          raise QbfException("Line %d.  Non-integer field" % lineNumber)
        # Last one should be 0
        if lits[-1] != 0:
          raise QbfException("Line %d.  Clause line should end with 0" % lineNumber)
        lits = lits[:-1]
        vars = sorted([abs(l) for l in lits])
        if len(vars) == 0:
          raise QbfException("Line %d.  Empty clause" % lineNumber)
        if vars[-1] > self.nvar or vars[0] == 0:
          raise CnfException("Line %d.  Out-of-range literal" % lineNumber)
        for i in range(len(vars) - 1):
          if vars[i] == vars[i+1]:
            raise QbfException("Line %d.  Opposite or repeated literal" % lineNumber)
        match = True
        if vars[-1] in self.variable_clauses:
          for clsidP in self.variable_clauses[vars[-1]]:
            litsP = self.clauses[clsidP]
            if len(litsP) < len(lits):
              match = False
              continue
            match = True
            for l in litsP:
              if l not in lits:
                match = False
                break
            if match: break
          if match: # Do not accept repeated clauses
            self.ncls -= 1
            continue
        
        self.clauses.append(lits)
        for v in vars:
            if v in self.variable_clauses:
                self.variable_clauses[v].append(clscnt)
            else:
               self.variable_clauses[v] = [clscnt]
        clscnt += 1
        
    if clscnt != self.ncls:
      raise QbfException("Line %d: Got %d clauses.  Expected %d" % (lineNumber, clscnt, self.ncls))
    
    self.nqlevels = qlevel
    
    file.close()

  # Read definitions into Definitions information
  # input format:
  #   'DefinitionType' <Int> 'OutLit' <Int>
  #   clauses (not 0 terminated)
  #   'endG'
  #
  # Definition Types:
  # 0: exotic (not pattern matched; semantic check)
  # 1: equivalence
  # 2: and
  # 3: or
  # 4: xor (full pattern in cnftools: not, xor, nxor, maj3, etc..)
  # 5: ite
  # 10: Monotonic
  #
  # XOR/Equivalence/Semantic/Monotonic definitions read into XOR information
  def read_definitions(self, fname):
    file = open(fname, 'r')
    lineNumber = 0
    definitioncnt = 0
    d_out = 0
    d_type = 0
    d_clauses = []
    d_inputs = []
    is_mon_out = [0] * self.ncls
    is_xor_clause = [0] * self.ncls
    
    broken_clause = False # Clause not found in input QBF
    xorcnt = 0
    scrap_definition = False
    repeated_XOR = False
    for line in file:
      lineNumber += 1
      line = trim(line)
      if len(line) == 0:
        continue
      elif line[0] == 'c':
        continue
      elif line[0:8] == 'GateType': # Start of new definition
        scrap_definition = False
        broken_clause = False
        repeated_XOR = False
        fields = line.split()
        d_type = int(fields[1])
        d_out = int(fields[3])

        if self.quantifiers[self.variable_qlevel[abs(d_out)]][0] == 'a' and (d_type == 2 or d_type == 3 or d_type == 5): # definitionoutput is universal lit
          self.definitions_on_universal += 1
          scrap_definition = True
        if self.quantifiers[self.variable_qlevel[abs(d_out)]][0] == 'a' and d_type == 10:
          self.definitions_on_universal += 1
        
        d_clauses = []
        d_inputs = []
      elif broken_clause: continue # consume lines until next new definition
      elif scrap_definition: continue
      elif repeated_XOR: continue
      elif line[0:4] == 'endG':    # end of a definition
        if d_type == 10: is_mon_out[abs(d_out)] = 1
        
        d_inputs = list(set(d_inputs))
        d_inputs.remove(abs(d_out))        # input variables of definition
        
        if d_type == 1 or d_type == 4 or d_type == 0 or d_type == 10: # Possibly XOR type definition
          self.xor_definitions.append(Definition(d_out, d_clauses, d_inputs, d_type))
          for v in d_inputs + [abs(d_out)]: # map vid to xor definition
            if v in self.variable_xor_definitions:
              self.variable_xor_definitions[v].append(xorcnt)
            else:
              self.variable_xor_definitions[v] = [xorcnt]
          xorcnt += 1
        else:
          self.definitions.append(Definition(d_out, d_clauses, d_inputs, d_type))
          for v in d_inputs: # map vid to definition as input
            if v in self.variable_g_in:
              self.variable_g_in[v].append(definitioncnt)
            else:
              self.variable_g_in[v] = [definitioncnt]
          self.is_definition_out[abs(d_out)] = 1
          definitioncnt += 1
      else: # read in a defining clause for current definition
        try:
          lits = [int(s) for s in line.split()]
        except:
          raise DefinitionException("Line %d.  Non-integer field" % lineNumber)
        clsID = self.find_cls(lits) # Find clause in current clause db
        if clsID == -1:             # clause not found, this definition is broken
          broken_clause = True
          print("e Broken clause in definition file Line %d." % lineNumber)
          continue
        if clsID in d_clauses:
          broken_clause = True
          print("e Repeated clause %d." % lineNumber) # Should never occur
          continue # no repeated clauses
        if d_type == 1 or d_type == 4 or d_type == 0: # avoid rereading same definition (monotonic excluded because def may be different)
          if is_xor_clause[clsID] == 1:
            repeated_XOR = True
            continue
          is_xor_clause[clsID] = 1
          self.clauses_xor_definitions[clsID] = xorcnt
        d_clauses.append(clsID)
        d_inputs += [abs(l) for l in lits]
      
    file.close()
    self.ndefinitions = definitioncnt
    self.nxor_definitions = xorcnt
      
  # Return clsid in current db: self.clauses
  #  -1 if not found
  def find_cls(self, lits):
    min_occ = len(self.variable_clauses[abs(lits[0])])
    min_var = abs(lits[0])
    # get variable with least occurences before checking for exact match
    for l in lits[1:]:
      v = abs(l)
      if len(self.variable_clauses[v]) < min_occ:
        min_var = v
        min_occ = len(self.variable_clauses[v])
    # TDOD: clause mask for faster check
    for cls in self.variable_clauses[min_var]:
      eq = True
      if len(self.clauses[cls]) != len(lits): continue
      for l in self.clauses[cls]:
        if l not in lits:
          eq = False
          break
      if eq: return cls
    return -1
    
    
  #####################################################################################
  # DEFINITION PROCESSING FUNCTIONS
  # MOVE DEFINITION OUTPUTS IN ORDER, CHECK DEFINITIONS ARE VALID
  #####################################################################################
    
  # in_l <= out_l
  def q_distance(self, in_l, out_l) :
    cnt = 0
    for i in range(in_l,out_l):
      if self.quantifiers[i][0] == 'a': cnt += 1
    return cnt
    
  def propagate_definition_move(self,moved_g):
    if moved_g in self.variable_g_in:
      for gidx in self.variable_g_in[moved_g]:
        g = self.definitions[gidx]
        (inner_l, inner_v) = self.get_innermost_level([self.var_map[i] for i in g.inputs])
        out_l = self.variable_qlevel[abs(g.outlit)]
        if out_l - inner_l > 1: # dist == 1 for pseudo
          if self.is_T_level(inner_l): self.candidate_lists[inner_l].append((gidx, False))
          else: self.candidate_lists[inner_l+1].append((gidx, False)) # +1 for T-level
        elif out_l - inner_l < 0:
          self.definitions_out_of_order += 1
        elif self.pseudo and (out_l - inner_l == 1) and self.is_T_level(inner_l):
          self.candidate_lists[inner_l].append((gidx, False))
    if moved_g in self.variable_xor_definitions:
      for gidx in self.variable_xor_definitions[moved_g]:
        if self.seen_xor[gidx] == 1: continue
        g = self.xor_definitions[gidx]
        (out_l, out_v) = self.get_innermost_level([self.var_map[i] for i in (g.inputs+[abs(g.outlit)])])
        (inner_l, inner_v) = self.get_innermost_level([self.var_map[i] for i in (g.inputs+[abs(g.outlit)]) if i != out_v])
        inner_v = self.reverse_var_map[inner_v]
        out_v = self.reverse_var_map[out_v]
        if inner_l == out_l or inner_l == out_l-1: continue
        if self.is_definition_out[out_v] == 1: continue
        if out_l - inner_l > 1: # dist == 1 for pseudo
          if not (out_v == abs(g.outlit)):
            self.xor_definitions[gidx].inputs.append(abs(g.outlit))
            self.xor_definitions[gidx].inputs.remove(out_v)
            if g.type == 10: self.definitions_out_of_order += 1 # check mono but not for XOR
          self.xor_definitions[gidx].outlit = out_v # lost sign on output variable for XOR
          if self.is_T_level(inner_l): self.candidate_lists[inner_l].append((gidx, True))
          else: self.candidate_lists[inner_l+1].append((gidx, True)) # +1 for T-level
        elif self.pseudo and (out_l - inner_l == 1) and self.is_T_level(inner_l):
          if inner_v not in self.xor_definitions[gidx].inputs:
            self.xor_definitions[gidx].inputs.append(inner_v)
            self.xor_definitions[gidx].inputs.remove(out_v)
          self.xor_definitions[gidx].outlit = out_v # lost sign on output variable for XOR
          self.candidate_lists[inner_l].append((gidx, True))
  
  def move(self,gidx, is_xor, level):
    # find level to be moved
    if is_xor == 1:
      g = self.xor_definitions[gidx]
    else:
      g = self.definitions[gidx]
    d_out = abs(g.outlit)
    
    (inner_l, inner_v) = self.get_innermost_level([self.var_map[i] for i in g.inputs])
    if inner_l != level and inner_l+1 != level:
      print("e candidate level and actual level do not match for d_out %d" % (g.outlit))

    dist = self.q_distance(level,self.variable_qlevel[d_out])
    if dist < 1 and not self.pseudo:
      return False
      
    # check not universal variable for XOR
    if self.quantifiers[self.variable_qlevel[abs(d_out)]][0] == 'a':
      self.definitions_on_universal += 1
      return False
    
    proved = self.prove_definition_move(gidx, self.variable_qlevel[d_out], level, is_xor) # correct input?
    
    if not proved:
      self.nvar -= 1
      return False
    
    self.total_nlevels_moved += dist
    self.ndefinitions_moved += 1
    self.var_moved[d_out] = 1
    self.is_definition_out[d_out] = 1 # for XOR definitions
    self.actual_move_type[d_out] = g.type
    if g.type == 4 : self.nxor_moved += 1
    if g.type == 0: self.nsemantic_moved += 1
    
    return True
  
  def get_innermost_level(self, vars):
    levels = [self.variable_qlevel[v] for v in vars]
    inner_l = 0
    inner_v = 0
    for i in range(len(vars)):
      if levels[i] >= inner_l:
        inner_v = vars[i]
        inner_l = levels[i]
    return (inner_l, inner_v)
    
  def is_T_level(self,level): return (level % 2 == 1)
  
  def move_by_level(self):
    self.seen_n = [0] * self.ndefinitions
    self.seen_xor = [0] * self.nxor_definitions
    self.candidate_lists = []
    for i in range(self.nqlevels): self.candidate_lists.append([])
    
    # initialize candidate_lists
    for gidx in range(self.ndefinitions):
      g = self.definitions[gidx]
      (inner_l, inner_v) = self.get_innermost_level([self.var_map[i] for i in g.inputs])
      out_l = self.variable_qlevel[abs(g.outlit)]
      if out_l - inner_l > 0:
        self.candidate_lists[inner_l+1].append((gidx, False)) # +1 for T-level
      elif out_l - inner_l < 0:
        self.definitions_out_of_order += 1
    for gidx in range(self.nxor_definitions):
      g = self.xor_definitions[gidx]
      (out_l, out_v) = self.get_innermost_level([self.var_map[i] for i in (g.inputs+[abs(g.outlit)])])
      (inner_l, inner_v) = self.get_innermost_level([self.var_map[i] for i in (g.inputs+[abs(g.outlit)]) if i != out_v])
      if inner_l == out_l or inner_l == out_l-1: continue
      if self.is_definition_out[out_v] == 1: continue
      if out_l - inner_l > 0:
        if not (out_v == abs(g.outlit)):
            self.xor_definitions[gidx].inputs.append(abs(g.outlit))
            self.xor_definitions[gidx].inputs.remove(out_v)
            if g.type == 10: self.definitions_out_of_order += 1 # check mono but not for XOR
        self.xor_definitions[gidx].outlit = out_v # lost sign on output variable for XOR
        self.candidate_lists[inner_l+1].append((gidx, True)) # +1 for T-level

    # move by level
    for level in range(0,self.nqlevels-2): # will skip non T-levels which have no candidates...
      while len(self.candidate_lists[level]) > 0:
        (gidx,is_xor) = self.candidate_lists[level].pop(0)
        if is_xor :
          if self.seen_xor[gidx] == 1: continue
          else: self.seen_xor[gidx] = 1
          if self.var_moved[abs(self.xor_definitions[gidx].outlit)] == 1: continue
        if not is_xor:
          if self.seen_n[gidx] == 1: continue
          else: self.seen_n[gidx] = 1
          if self.var_moved[abs(self.definitions[gidx].outlit)] == 1: continue
        moved = self.move(gidx,is_xor,level)
        if moved:
          if is_xor == 1: self.propagate_definition_move(abs(self.xor_definitions[gidx].outlit))
          else:self.propagate_definition_move(abs(self.definitions[gidx].outlit))


  def prove_definition_move(self, gidx, old_level, max_level, is_xor):
    if is_xor == 1: g = self.xor_definitions[gidx]
    else: g = self.definitions[gidx]
    d_outlit = g.outlit
    d_out = abs(d_outlit)
    d_clauses = g.clauses
    d_inputs = [self.var_map[i] for i in g.inputs]
    d_type = g.type
    self.nvar += 1
    new_var = self.nvar
    one_sided = True
    one_sided_lit = 0
    sign_l = int(d_outlit/(abs(d_outlit)))
    aux = (d_type not in [1,2,3]) or (len(d_clauses) != 2 or len(d_inputs) != 1)
    bic = d_type != 1 or (len(d_clauses) != 2 or len(d_inputs) != 1)
    
    new_d_clauses = []
    old_d_clauses = []
    clause_updates = []
    delete_list = []
    proof_list = []
    
    bicond1 = None
    bicond2 = None

    # STEP 1: ADD Defining clauses for x' = new_var
    for clsid in d_clauses:
      cls = self.clauses[clsid]
      if d_type == 10 and (d_out not in cls and -d_out not in cls):
        return False # incorrectly using it as an XOR, i.e., clauses do not define d_out
      if one_sided: # check if one-sided definition
        if one_sided_lit == 0:
          one_sided_lit = [v for v in cls if abs(v) == d_out][0]
        else:
          lit = [v for v in cls if abs(v) == d_out][0]
          if lit != one_sided_lit:
            one_sided = False
      new_cls = cls[:]
      if d_out in new_cls:
        new_cls.remove(d_out)
        new_cls = [new_var] + new_cls
      else:
        new_cls.remove(-d_out)
        new_cls = [-new_var] + new_cls
      old_d_clauses.append(cls)
      new_d_clauses.append(new_cls)
      
      proof_list.append((0,new_cls[:]))
      clause_updates.append((clsid,new_cls[:])) # cannot add them right away in case process fails
      
    aux = aux and not one_sided
     
    # STEP 2: ADD BiEquivalence x <-> x' clauses
    if one_sided: # definition output appears as one sided literal (not fully-defined)
      bicond1 = [sign_l*new_var, -1*d_outlit]
      proof_list.append((0,bicond1))
      bic = False
    
    if bic: # add first side
      bicond2 = [new_var,-d_out]
      proof_list.append((0,bicond2))

    
    if aux: # derive other side
      aux_clauses = self.biconditional_aux_resolvents(d_out, new_var, old_d_clauses, new_d_clauses, d_inputs)
      if len(aux_clauses) == 0:
        self.print_verb("c Failed finding auxilliary clauses for %d" % (d_out),1)
        self.definitions_notdefined += 1
        return False
      
      last_clause = aux_clauses[-1]
      if last_clause != [d_out, -new_var] and last_clause != [ -new_var, d_out]:
        self.print_verb("c Failed finding auxilliary clauses for %d" % (d_out),1)
        self.definitions_notdefined += 1
        return False
      # ADD Auxiliary clauses
      for cls in aux_clauses[:-1]:
        proof_list.append((0,cls))
    
    if bic: # ADD other implication
      bicond1 = [d_out, -new_var]
      proof_list.append((0,bicond1))

    if aux: # REMOVE Auxiliary clauses
      aux_clauses = aux_clauses[:-1]
      aux_clauses.reverse()
      for cls in aux_clauses:
        proof_list.append((1,cls))
      
    # STEP 3: ADD/DELETE Remaining clauses
    for clsID in self.variable_clauses[d_out]:
      if clsID in d_clauses: continue
      cls = self.clauses[clsID]
      new_cls = [int (v/abs(v)) * new_var if abs(v) == d_out else v for v in cls]
      g_temp = new_var
      if -new_var in new_cls:
        g_temp = -new_var
        new_cls.remove(-new_var)
      else: new_cls.remove(new_var)
      new_cls = [g_temp] + new_cls
      
      g_temp = d_out
      old_cls = cls[:]
      if -d_out in old_cls:
        g_temp = -d_out
        old_cls.remove(-d_out)
      else: old_cls.remove(d_out)
      old_cls = [g_temp] + old_cls
      
      proof_list.append((0,new_cls))
      
      clause_updates.append((clsID,new_cls[:]))
      if one_sided:
        tcls = cls[:]
        g_temp = d_out
        if -d_out in tcls:
          if -one_sided_lit != -d_out: #not actually one-sided (w.r.t. remaining clauses)
            self.definitions_one_sided_incorrect += 1
            return False
          g_temp = -d_out
          tcls.remove(-d_out)
        else:
          if -one_sided_lit != d_out: #not actually one-sided
            self.definitions_one_sided_incorrect += 1
            return False
          tcls.remove(d_out)
        tcls = [g_temp] + tcls
        delete_list.append(tcls)
      else:proof_list.append((1,old_cls))
     
    # STEP 4: DELETE BiEquivalence
    if bic:
      bicond2 = [-d_out, new_var] # change order fo QRAT check
      bicond1 = [d_out, -new_var]
      proof_list.append((1,bicond1))
      proof_list.append((1,bicond2))
    
    # STEP 5: DELETE Defining clauses of x
    for clsid in d_clauses:
      cls = self.clauses[clsid]
      g_temp = d_out
      if -d_out in cls:
        g_temp = -d_out
        cls.remove(-d_out)
      else: cls.remove(d_out)
      cls = [g_temp] + cls
      proof_list.append((1,cls[:]))
      
    if one_sided:
      for d in delete_list:
        proof_list.append((1,d))
      proof_list.append((1,[bicond1[1],bicond1[0]]))
      
    if not self.prove_no_write:
      for d,c in proof_list: self.write_clause(self.proof,c,d==1)
    
    # UPDATE CLAUSE DICTIONARY
    for (clsid,new_cls) in clause_updates:
      self.clauses[clsid] = new_cls
    
    self.variable_clauses[new_var] = self.variable_clauses[d_out]
    self.quantifiers[old_level][1].remove(d_out)
    self.quantifiers[max_level][1].append(new_var)
    self.variable_qlevel[new_var] = max_level
    self.var_map[d_out] = new_var
    self.var_map.append(new_var)
    self.reverse_var_map.append(d_out)

    if one_sided: self.one_sided_moves += 1

    return True

  #####################################################################################
  # DEFINING VARIABLE ELIMINATION
  #####################################################################################
  
  # Definition is not Eq, AND, OR
  # Need auxillary clauses to prove biconditional between old definition variable
  #  and new definition variable
  #
  # Use basic variable elimination technique for Q-resolution proof, eliminating
  #   inputs until only the two definition outputs are left
  def biconditional_aux_resolvents(self, d_out, new_var, old_d_clauses, new_d_clauses, d_inputs):
    pos_old_g = [cls for cls in old_d_clauses if d_out in cls]
    neg_new_g = [cls for cls in new_d_clauses if -new_var in cls]
    clauses = pos_old_g + neg_new_g
    nclauses = len(clauses)
    orig_clauses = nclauses
    active_caluses = [1] * nclauses
    variable_clauses = {}
    for idx in d_inputs + [d_out, new_var]: variable_clauses[idx] = [[],[]]
    for clsidx in range(len(clauses)):
      for l in clauses[clsidx]:
        variable_clauses[abs(l)][int(l>0)].append(clsidx)
    bps = [0] * orig_clauses
    aux_clauses = []
    found = False
    res_cnt = 0
    step_first = True
    # eliminate inputs one at a time with var. elim. by distribution
    for g_in in d_inputs:
#      print("Eliminating %d" % (g_in))
      pos_clauses = variable_clauses[g_in][1]
      ned_clauses = variable_clauses[g_in][0]
#      print(pos_clauses)
#      print(ned_clauses)
      for p_clause in pos_clauses:
        if not active_caluses[p_clause]: continue
        p_lits = clauses[p_clause]
        for n_clause in ned_clauses:
          if not active_caluses[n_clause]: continue
          n_lits = clauses[n_clause]
#          print("RESOLVING")
#          print(p_lits)
#          print(n_lits)
          resolventT = p_lits + n_lits
          resolventT.remove(g_in)
          resolventT.remove(-g_in)
          if step_first: # only consider resolvents containing both -new_var and d_out
            if not d_out in resolventT or not -new_var in resolventT:
              continue
          resolvent = []
          taut = False
          for r in resolventT:
            if r not in resolvent: resolvent.append(r)
            if -r in resolvent:
              taut = True
              break
          if not taut:
            for l in resolvent:
              variable_clauses[abs(l)][int(l>0)].append(nclauses)
#            print(resolvent)
            clauses.append(resolvent)
            aux_clauses.append(resolvent)
            active_caluses.append(1)
            bps.append([p_clause,n_clause])
            nclauses += 1
            if resolvent == [d_out, -new_var]:
              found = True
              break
        if found: break
      for clsid in pos_clauses + ned_clauses:
        active_caluses[clsid] = 0
      if found: break
      step_first = False

    # get derivation chain
    if len(aux_clauses) < 1 or aux_clauses[-1] != [-new_var, d_out] and aux_clauses[-1] != [d_out,-new_var] : # Failed
      return aux_clauses
    
    derivation_chain = [aux_clauses[-1]]
    front = bps[-1]
    seen = [0] * nclauses
    while front:
      clsid = front.pop(0)
      if clsid < orig_clauses: continue
      if seen[clsid] == 1: continue
      derivation_chain.append(clauses[clsid])
      front += bps[clsid]
      seen[clsid] = 1
      
    derivation_chain.reverse()
    
    return derivation_chain
  
  
  #######################################################################################
  # WRITING AND MISCL. FUNCTIONS
  #######################################################################################
  
  def write_qbf(self, fname):
    file = open(fname, 'w')
    file.write("p cnf %d %d\n" % (self.nvar, self.ncls))
    for (qt, ql) in self.quantifiers:
      self.print_verb(ql,1)
      if ql == []: continue
      ilist = ql + [0]
      slist = [str(i) for i in ilist]
      slist = [qt] + slist
      istring = " ".join(slist)
      file.write(istring + '\n')
    for lits in self.clauses:
      ilist = lits + [0]
      slist = [str(i) for i in ilist]
      istring = " ".join(slist)
      file.write(istring + '\n')


  # -- Definition output --
  # Written in order from inputs to outputs
  # for each definition,
  # DefinitionInputs:
  # DefinitionInputTseitens:
  # DefinitionOutput:
  def write_definitions(self, fname):
    file = open(fname, 'w')
    init_definitions = self.initial_definitions()
    seen = [0] * (self.nvar+1) # definition output seen in bfs
    support = {}
    q = Queue()
    for gidx in init_definitions: q.put(gidx)
    # BFS across definitions, following input to output ordering
    while not q.empty():
      gidx = q.get()
      g = self.definitions[gidx]
      d_outlit = g.outlit
      d_out = abs(d_outlit)
      d_inputs = g.inputs
      variables = d_inputs + [d_out]
      if seen[d_out]: continue
      # check other inputs
      if any([not seen[v] for v in d_inputs if self.is_definition_out[v]]):
        continue # other input definitions need to be processed (seen) first
      seen[d_out] = 1 # definition has been processed
      # add new definitions where d_out is input
      if d_out in self.variable_g_in:
        for ng in self.variable_g_in[d_out]: q.put(ng)
      # Move in qnf
      self.write_definition(gidx, file)
  
  def write_definition(self,gidx,file):
    g = self.definitions[gidx]
    d_outlit = g.outlit
    d_out = abs(d_outlit)
    d_inputs = g.inputs
    ilist = d_inputs
    slist = [str(i) for i in ilist]
    istring = " ".join(slist)
    file.write("DefinitionInputs: " + istring + "\n")
    tseitens = [v for v in d_inputs if self.is_definition_out[v]]
    ilist = tseitens
    slist = [str(i) for i in ilist]
    istring = " ".join(slist)
    file.write("DefinitionInputTseitens: "+ istring + "\n")
    file.write("DefinitionOutput: %d\n\n" % (d_outlit))
  
  def write_comment(self, file, comment):
    file.write("c "+comment+"\n")
    
  def write_clause(self, file, clause, delete = False):
    ilist = clause + [0]
    slist = [str(i) for i in ilist]
    if delete : slist = ['d'] + slist
    istring = " ".join(slist)
    file.write(istring + '\n')
  def print_stats(self):
    if self.tool == "cnf-mv":
      header = ["Tool", "Not LU Existential", "Not LU Universal", "Not One-Sided", "One-Sided Moved"]
      line ='%-10s %-20s %-20s %-20s %-20s' % (header[0],header[1],header[2],header[3], header[4])
      print("-")
      print(line)
    line ='%-10s %-20s %-20s %-20s %-20s' % (self.tool , self.definitions_out_of_order,self.definitions_on_universal,self.definitions_one_sided_incorrect+self.definitions_notdefined, self.one_sided_moves)
    print(line)
  
  
#    print("Statistics")
#    print("Number of definitions: "+str(self.ndefinitions))
#    print("Number of XORs and Semantic and Monotonic: "+str(self.nxor_definitions))
#    print("Number of definitions moved: "+str(self.ndefinitions_moved))
#    print("Number of definitions incorrect out of order: "+str(self.definitions_out_of_order))
#    print("Number of definitions incorrect on universal: "+str(self.definitions_on_universal))
#    print("Number of definitions incorrect not defined: "+str(self.definitions_notdefined))
#    print("Number of definitions incorrect one-sided: "+str(self.definitions_one_sided_incorrect))
#    if self.ndefinitions_moved > 0:
#      print("Total difference in levels for moved variables: "+str(self.total_nlevels_moved))
#      print("Average difference in levels for moved variables: "+str(self.total_nlevels_moved/self.ndefinitions_moved))
#      print("One-sided moves: "+str(self.one_sided_moves))
  
  def print_verb(self, st, verb):
    if verb <= self.verbosity:
      print(st)
  
  def print_var_map(self, fname):
    file = open(fname, 'w')
    for i in range(1,self.nvar_orig+1):
      if self.var_moved[i] == 1: file.write(str(i) +" "+str(self.var_map[i])+" " +str(self.actual_move_type[i]) +"\n")
  
#######################################################################################
# MAIN FUNCTION
#######################################################################################
  
def run(name, args):
    qbfName = None
    definitionName = None
    outqbfName = None
    outdefinitionName = None
    proofName = None
    prove_no_write = False
    move_definitions = False
    restrictDefinitions = False
    verbosity = 0
    var_map_name = None
    pseudo = False
    tool = None
    
    optlist, args = getopt.getopt(args, "swhdrmv:q:o:g:l:p:b:t:")
    for (opt, val) in optlist:
        if opt == '-h':
          usage(name)
          return
        elif opt == '-q':
          qbfName = val
        elif opt == '-g':
          definitionName = val
        elif opt == '-o':
          outqbfName = val
        elif opt == '-b':
          var_map_name = val
        elif opt == '-l':
          outdefinitionName = val
        elif opt == '-p':
          proofName = val
        elif opt == '-m':
          move_definitions = True
        elif opt == '-v':
          verbosity = int(val)
        elif opt == '-w':
          prove_no_write = True
        elif opt == '-r':
          restrictDefinitions = True
        elif opt == '-s':
          pseudo = True
        elif opt == '-t':
          tool = val
    
    qbf = QBF_Definition_Processor(qbfName, proofName, verbosity, prove_no_write,restrictDefinitions, pseudo, tool)
    
    qbf.read_definitions(definitionName)
  

    if move_definitions:
      qbf.move_by_level()
    
    if not outqbfName is None:
      qbf.write_qbf(outqbfName)
    
    if not outdefinitionName is None:
      qbf.write_definitions(outdefinitionName)
    
    if not var_map_name is None:
      qbf.print_var_map(var_map_name)
    
    qbf.print_stats()
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
