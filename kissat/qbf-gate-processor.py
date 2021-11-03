import sys
import getopt
import functools
import operator
from queue import Queue

def usage(name):
    sys.stderr.write("Usage: %s [-h] [-d] [-x] [-m] [-v LEVEL] [-q QNF]  [-o OUTQNF]  [-g GATE] [-l OUTGATE]" % name)
    sys.stderr.write("  -h          Print this message\n")
    sys.stderr.write("  -v LEVEL    Verbose output level 1: gate detection...\n")
    sys.stderr.write("  -q QNF      Name of QNF input file\n")
    sys.stderr.write("  -d          Input is DQBF file\n")
    sys.stderr.write("  -o OUTQNF   Name of Output QNF file\n")
    sys.stderr.write("  -g GATE     Name of GATE input file\n")
    sys.stderr.write("  -l OUTGATE  Name of Output GATE file with dependencies\n")
    sys.stderr.write("  -x          Process xor gates and add them with the determined output to total set of gates\n")
    sys.stderr.write("  -m          Move gate outputs to minimum possible quantifier level (Tseiten variable quantifier levels added in between original levels)\n")


def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

class QbfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "QBF Exception: " + str(self.value)
        
class GateException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Gate Exception: " + str(self.value)


class Gate():
  
  def __init__(self, g_outlit, g_clauses, g_inputs, g_type):
    self.outlit = g_outlit
    self.clauses = g_clauses
    self.inputs = g_inputs
    self.type = g_type

class QBF_Gate_Processor():
  
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
  
  # Gate information
  ngates = 0
  gates = []            # list of gates
  is_gate_out    = []   # vid -> 1 if vid is output of a gate, 0 otherwise
  variable_g_out = {}   # map: vid -> gate that vid is the output of
  variable_g_in  = {}   # map: vid -> gates that vid is the input of
  
  # XOR gate information
  nxor_gates = 0
  xor_gates = []          # list of xor gates (g_out, g_clauses, g_inputs)
                          #   g_out is the temporary gate output giving by the gate
                          #   definition. This may change in xor gate processing
  variable_xor_gates = {} # map: vid   -> xor gate ids with vid in defining clauses
  clauses_xor_gates  = {} # map: clsid -> xor gate id with clsid in definition
  
  # Gate processing information
  ngates_moved = 0      # number of gate outputs moved to lower qlevel
  ngates_incorrect = 0  # number of gate outputs that appear at lower level than
                        # variables in defining clauses (not proper gates in qbf)
  total_nlevels_moved=0 # sum of diff in level for each variable moved
  var_map = [0]         # map old variable IDs to new values (when introducing
                        # new Tseiten variables
  reverse_var_map = [0]
  actual_move_type = {}
  restrictGates = False
  
  one_sided_moves           = 0
  
  gates_out_of_order        = 0 # incorrect gate possibilities
  gates_on_universal        = 0
  gates_notdefined          = 0
  gates_one_sided_incorrect = 0
  nxor_moved                = 0
  nsemantic_moved           = 0
  
  last_level = []       # LDomino check on movement of variables in last Qlevel
  var_moved = None
  
  candidate_lists = None # move algorithm
  seen_n = None
  seen_xor = None
  
  proof = None
  writeProof = False
  prove_no_write = False

  def __init__(self, qbfName, proofName = None, verbosity = 0, prove_no_write = False, restrictGates = False, pseudo = False):
    if not proofName is None:
      self.proof = open(proofName, 'w')
      self.writeProof = True
    self.prove_no_write = prove_no_write
    self.restrictGates = restrictGates
    self.pseudo = pseudo

    self.read_qbf(qbfName)
    for i in range(1,self.nvar+1):
      self.var_map.append(i)
      self.reverse_var_map.append(i)
    self.verbosity = verbosity
    
    for i in self.quantifiers[-2][1]:
      self.last_level.append(i)
    self.var_moved = [0]*(self.nvar+1)
    self.nvar_orig = self.nvar
    
    
    
  #####################################################################################
  # PARSING FUNCTIONS
  # QBF, GATES
  #####################################################################################

    
  # Parser adapted from PGBDD, Randy E. Bryant
  # Read quantifiers and clauses into QBF information
  # Quantifier levels (qlevels) are read as even numbers 0,2,4,..
  #   odd numbered qlevels reserved for moved Tseiten variables
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
        self.is_gate_out = [0] * (self.nvar +1)
        getting_quantifiers = True
        
      elif line[0] == 'a' or line[0] == 'e':
        if not getting_quantifiers:
          raise QbfException("Line %d.  Quantifier out of order line '%s'.  Not qbf" % (lineNumber, line))
        try:
            vars = [int(s) for s in line[1:].split()]
        except:
            raise QbfException("Line %d.  Non-integer field" % lineNumber)
        # Last one should be 0
        if vars[-1] != 0:
            raise QbfException("Line %d.  Quantifier line should end with 0" % lineNumber)
        vars = vars[:-1]
        self.quantifiers.append((line[0],vars[:])) # Original quantifier level (Even index 0,2,4,...)
        self.quantifiers.append(('e',[])) # T-level following original quantifier level (Odd index 1,3,5,...)
        for v in vars: # check variable not in a previous qlevel
          if v in self.variable_qlevel:
            raise QbfException("Line %d.  %d in two quantifier levels.  Not qbf" % (lineNumber, v))
          self.variable_qlevel[v] = qlevel
        qlevel += 2 # reserve odds for Tseiten variables
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

  # Read gates into Gates information
  # input format:
  #   'GateType' <Int> 'OutLit' <Int>
  #   clauses (not 0 terminated)
  #   'endG'
  #
  # Gate Types:
  # 0: exotic (not pattern matched; semantic check)
  # 1: equivalence
  # 2: and
  # 3: or
  # 4: xor (full pattern in cnftools: not, xor, nxor, maj3, etc..)
  # 5: ite
  # 10: Monotonic
  #
  # XOR/Equivalence/Semantic gates read into XOR information
  #   Semantic gates could in fact be XOR types...
  def read_gates(self, fname):
    file = open(fname, 'r')
    lineNumber = 0
    gatecnt = 0
    g_out = 0
    g_type = 0
    g_clauses = []
    g_inputs = []
    is_mon_out = [0] * self.ncls
    is_xor_clause = [0] * self.ncls
    
    broken_clause = False # Clause not found in input QBF
    xorcnt = 0
    #gate_types = {0:'exotic',1:'equivalence',2:'and',3:'or',4:'xor',5:'ite'}
    scrap_gate = False
    repeated_XOR = False
    for line in file:
      lineNumber += 1
      line = trim(line)
      if len(line) == 0:
        continue
      elif line[0] == 'c':
        continue
      elif line[0:8] == 'GateType': # Start of new gate
        scrap_gate = False
        broken_clause = False
        repeated_XOR = False
        fields = line.split()
        g_type = int(fields[1])
        g_out = int(fields[3])
#        if g_type == 10 and is_mon_out[abs(g_out)] == 1:
#          repeated_XOR = True
#
        if self.quantifiers[self.variable_qlevel[abs(g_out)]][0] == 'a' and (g_type == 2 or g_type == 3 or g_type == 5): # gateoutput is universal lit
          self.gates_on_universal += 1
          scrap_gate = True
        
        g_clauses = []
        g_inputs = []
      elif broken_clause: continue # consume lines until next new gate
      elif scrap_gate: continue
      elif repeated_XOR: continue
      elif line[0:4] == 'endG':    # end of a gate
        if g_type == 10: is_mon_out[abs(g_out)] = 1
        
        g_inputs = list(set(g_inputs))
        g_inputs.remove(abs(g_out))        # input variables of gate
        
        if g_type == 1 or g_type == 4 or g_type == 0 or g_type == 10: # eq or xor
          self.xor_gates.append(Gate(g_out, g_clauses, g_inputs, g_type))
          for v in g_inputs + [abs(g_out)]: # map vid to xor gates
            if v in self.variable_xor_gates:
              self.variable_xor_gates[v].append(xorcnt)
            else:
              self.variable_xor_gates[v] = [xorcnt]
          xorcnt += 1
        else:
#          if self.is_gate_out[abs(g_out)] == 1:
#            if g_type == 10: continue
#            gidx = self.variable_g_out[abs(g_out)]
#            g = self.gates[gidx]
#            if g.type == 10: # replace with new gate
          self.gates.append(Gate(g_out, g_clauses, g_inputs, g_type))
          for v in g_inputs: # map vid to gate as input
            if v in self.variable_g_in:
              self.variable_g_in[v].append(gatecnt)
            else:
              self.variable_g_in[v] = [gatecnt]
          if g_type != 10: self.is_gate_out[abs(g_out)] = 1
          #self.variable_g_out[abs(g_out)] = gatecnt
          gatecnt += 1
      else: # read in a defining clause for current gate
        try:
          lits = [int(s) for s in line.split()]
        except:
          raise GateException("Line %d.  Non-integer field" % lineNumber)
        clsID = self.find_cls(lits) # Find clause in current clause db
        if clsID == -1:             # clause not found, this gate is broken
          broken_clause = True
          print("e Broken clause in gate file Line %d." % lineNumber)
          continue
        if clsID in g_clauses: continue # no repeated clauses?
        if g_type == 1 or g_type == 4 or g_type == 0: # eq or xor or semantic, map clsid -> xor gate id
          if is_xor_clause[clsID] == 1:
            repeated_XOR = True
#            print(self.clauses[clsID])
            continue
          is_xor_clause[clsID] = 1
          self.clauses_xor_gates[clsID] = xorcnt
        g_clauses.append(clsID)
        g_inputs += [abs(l) for l in lits]
      
    file.close()
    self.ngates = gatecnt
    self.nxor_gates = xorcnt
      
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
  # GATE PROCESSING FUNCTIONS
  # MOVE GATE OUTPUTS IN ORDER, CHECK GATES ARE VALID
  #####################################################################################
    
  def q_distance(self, in_l, out_l) :
    cnt = 0
    for i in range(in_l,out_l):
      if self.quantifiers[i][0] == 'a': cnt += 1
    return cnt
    
  def propagate_move(self,moved_g):
    if moved_g in self.variable_g_in:
      for gidx in self.variable_g_in[moved_g]:
        g = self.gates[gidx]
        (inner_l, inner_v) = self.get_innermost_level([self.var_map[i] for i in g.inputs])
        out_l = self.variable_qlevel[abs(g.outlit)]
        if out_l - inner_l > 1: # dist == 1 for pseudo
#          if abs(g.outlit) == 5938: print("Added on prpoagate")
          if self.is_T_level(inner_l): self.candidate_lists[inner_l].append((gidx, False))
          else: self.candidate_lists[inner_l+1].append((gidx, False)) # +1 for T-level
        elif out_l - inner_l < 0:
          self.gates_out_of_order += 1 # won't be checking this for semantic gates unfortunately...
        elif self.pseudo and (out_l - inner_l == 1) and self.is_T_level(inner_l):
          self.candidate_lists[inner_l].append((gidx, False))
    if moved_g in self.variable_xor_gates:
      for gidx in self.variable_xor_gates[moved_g]:
        if self.seen_xor[gidx] == 1: continue
        g = self.xor_gates[gidx]
        (out_l, out_v) = self.get_innermost_level([self.var_map[i] for i in (g.inputs+[abs(g.outlit)])])
        (inner_l, inner_v) = self.get_innermost_level([self.var_map[i] for i in (g.inputs+[abs(g.outlit)]) if i != out_v])
        inner_v = self.reverse_var_map[inner_v]
        out_v = self.reverse_var_map[out_v]
        if inner_l == out_l or inner_l == out_l-1: continue
        if self.is_gate_out[out_v] == 1: continue
        if out_l - inner_l > 1: # dist == 1 for pseudo
          if not (out_v == abs(g.outlit)):
            self.xor_gates[gidx].inputs.append(abs(g.outlit))
            self.xor_gates[gidx].inputs.remove(out_v)
          self.xor_gates[gidx].outlit = out_v # lost sign on output variable for XOR
          if self.is_T_level(inner_l): self.candidate_lists[inner_l].append((gidx, True))
          else: self.candidate_lists[inner_l+1].append((gidx, True)) # +1 for T-level
        elif self.pseudo and (out_l - inner_l == 1) and self.is_T_level(inner_l):
          if inner_v not in self.xor_gates[gidx].inputs:
            self.xor_gates[gidx].inputs.append(inner_v)
            self.xor_gates[gidx].inputs.remove(out_v)
          self.xor_gates[gidx].outlit = out_v # lost sign on output variable for XOR
          self.candidate_lists[inner_l].append((gidx, True))
    # check if already seen...
  
  def move(self,gidx, is_xor, level):
    # find level to be moved
    if is_xor == 1:
      g = self.xor_gates[gidx]
    else:
      g = self.gates[gidx]
    g_out = abs(g.outlit)
    
#    if g_out == 119: print("MOVE")
    (inner_l, inner_v) = self.get_innermost_level([self.var_map[i] for i in g.inputs])
    if inner_l != level and inner_l+1 != level:
#      if g_out == 119: print("error")
      print("e candidate level and actual level do not match for g_out %d" % (g.outlit))
    
#    print("ATTEMPT "+ str(g_out))
#    print(g.inputs)
#    print([self.var_map[i] for i in g.inputs])
#    print(inner_l)
#    print(level)
    dist = self.q_distance(level,self.variable_qlevel[g_out])
    if dist < 1 and not self.pseudo:
#      print("e: distance of movement not at least 1 for g_out %d" % (g.outlit))
      return False
    # check not universal variable for XOR
    if self.quantifiers[self.variable_qlevel[abs(g_out)]][0] == 'a':
      self.gates_on_universal += 1
      return False
    
    proved = self.prove_gate_move(gidx, self.variable_qlevel[g_out], level, is_xor) # correct input?
    
    if not proved:
      self.nvar -= 1
      return False
    
    self.total_nlevels_moved += dist
    self.ngates_moved += 1
    self.var_moved[g_out] = 1
    self.is_gate_out[g_out] = 1 # for XOR gates
    self.actual_move_type[g_out] = g.type
    if g.type == 4 : self.nxor_moved += 1
    if g.type == 0: self.nsemantic_moved += 1
    
#    if (g_out == 5938):
#    print("MOVED "+ str(g_out))
#    print(g.inputs)
#    print([self.var_map[i] for i in g.inputs])
#    print(inner_l)
#    print(level)
    
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
    self.seen_n = [0] * self.ngates
    self.seen_xor = [0] * self.nxor_gates
    self.candidate_lists = []
    for i in range(self.nqlevels): self.candidate_lists.append([])
    
    # initialize candidate_lists
    for gidx in range(self.ngates):
      g = self.gates[gidx]
      (inner_l, inner_v) = self.get_innermost_level([self.var_map[i] for i in g.inputs])
      out_l = self.variable_qlevel[abs(g.outlit)]
      if out_l - inner_l > 0:
        self.candidate_lists[inner_l+1].append((gidx, False)) # +1 for T-level
#        if abs(g.outlit) == 5938: print("Added on initialization")
      elif out_l - inner_l < 0:
        self.gates_out_of_order += 1 # won't be checking this for semantic gates unfortunately...
    for gidx in range(self.nxor_gates):
      g = self.xor_gates[gidx]
      (out_l, out_v) = self.get_innermost_level([self.var_map[i] for i in (g.inputs+[abs(g.outlit)])])
      (inner_l, inner_v) = self.get_innermost_level([self.var_map[i] for i in (g.inputs+[abs(g.outlit)]) if i != out_v])
      if inner_l == out_l or inner_l == out_l-1: continue
      if self.is_gate_out[out_v] == 1: continue
      if out_l - inner_l > 0:
        if not (out_v == abs(g.outlit)):
            self.xor_gates[gidx].inputs.append(abs(g.outlit))
            self.xor_gates[gidx].inputs.remove(out_v)
        self.xor_gates[gidx].outlit = out_v # lost sign on output variable for XOR
        self.candidate_lists[inner_l+1].append((gidx, True)) # +1 for T-level

    # move by level
#    for l in self.candidate_lists: print(l)
    for level in range(0,self.nqlevels-2): # will skip non T-levels which have no candidates...
      while len(self.candidate_lists[level]) > 0:
        (gidx,is_xor) = self.candidate_lists[level].pop(0)
        if is_xor :
          if self.seen_xor[gidx] == 1: continue
          else: self.seen_xor[gidx] = 1
          if self.var_moved[abs(self.xor_gates[gidx].outlit)] == 1: continue
        if not is_xor:
          if self.seen_n[gidx] == 1: continue
          else: self.seen_n[gidx] = 1
          if self.var_moved[abs(self.gates[gidx].outlit)] == 1: continue
        moved = self.move(gidx,is_xor,level)
        if moved:
          if is_xor == 1: self.propagate_move(abs(self.xor_gates[gidx].outlit))
          else:self.propagate_move(abs(self.gates[gidx].outlit))


  def prove_gate_move(self, gidx, old_level, max_level, is_xor):
    if is_xor == 1: g = self.xor_gates[gidx]
    else: g = self.gates[gidx]
    g_outlit = g.outlit
    g_out = abs(g_outlit)
    g_clauses = g.clauses
    g_inputs = [self.var_map[i] for i in g.inputs]
    g_type = g.type
    self.nvar += 1
    new_var = self.nvar
    one_sided = True
    one_sided_lit = 0
    sign_l = int(g_outlit/(abs(g_outlit)))
    aux = (g_type not in [1,2,3]) or (len(g_clauses) != 2 or len(g_inputs) != 1)
    bic = g_type != 1 or (len(g_clauses) != 2 or len(g_inputs) != 1)
    
#    self.write_comment(self.proof,"add gate for new variable %d" %(new_var))
    new_g_clauses = []
    old_g_clauses = []
    clause_updates = []
    delete_list = []
    proof_list = []
    
    bicond1 = None
    bicond2 = None
#    if new_var == 2832:
#      print(g_inputs)
#    print("")
#    print(g_out)
    for clsid in g_clauses:
#      print (clsid)
      cls = self.clauses[clsid]
      if g_type == 10 and (g_out not in cls and -g_out not in cls):
        return False # incorrectly using it as an XOR
      if one_sided:
        if one_sided_lit == 0:
          one_sided_lit = [v for v in cls if abs(v) == g_out][0]
        else:
          lit = [v for v in cls if abs(v) == g_out][0]
          if lit != one_sided_lit:
            one_sided = False
      new_cls = cls[:]
      if g_out in new_cls:
        new_cls.remove(g_out)
        new_cls = [new_var] + new_cls
      else:
        new_cls.remove(-g_out)
        new_cls = [-new_var] + new_cls
      old_g_clauses.append(cls)
      new_g_clauses.append(new_cls)
      
      proof_list.append((0,new_cls[:]))
#      if not self.prove_no_write: self.write_clause(self.proof, new_cls)
      
      clause_updates.append((clsid,new_cls[:])) # cannot add them right away in case process fails
     
    aux = aux and not one_sided
     
    if one_sided: # gate output appears as one sided literal (not defined)
      bicond1 = [sign_l*new_var, -1*g_outlit]
#      if not self.prove_no_write: self.write_clause(self.proof,bicond1)
      proof_list.append((0,bicond1))
      bic = False
    
    if bic: # add first side
      bicond2 = [new_var,-g_out]
      proof_list.append((0,bicond2))
#      if not self.prove_no_write: self.write_clause(self.proof,bicond2)
    
    if aux: # derive other side

      aux_clauses = self.biconditional_aux_resolvents(g_out, new_var, old_g_clauses, new_g_clauses, g_inputs)
      
      if len(aux_clauses) == 0:
        print("e Failed finding auxilliary clauses for %d" % (g_out))
#        print(last_clause)
        self.gates_notdefined += 1
        return False
      
      last_clause = aux_clauses[-1]
      if last_clause != [g_out, -new_var] and last_clause != [ -new_var, g_out]:
        # Variable elimination got rid of old gate and new gate variables
        # No need for auxillary clauses in this case?
        
        print("e Failed finding auxilliary clauses for %d" % (g_out))
#        print(last_clause)
        self.gates_notdefined += 1
        return False# no biconditional found (any gates missed here that shouldn't be?)
        aux = False
      
      for cls in aux_clauses[:-1]:
        proof_list.append((0,cls))
#          if not self.prove_no_write: self.write_clause(self.proof,cls)
    
#    self.write_comment(self.proof,"add biconditional %d <-> %d" %(new_var, g_out))
    if bic:
      bicond1 = [g_out, -new_var]
#      if not self.prove_no_write: self.write_clause(self.proof,bicond1)
      proof_list.append((0,bicond1))
      
      #    self.write_comment(self.proof,"delete auxillary clauses for biconditional %d <-> %d" %(new_var, g_out))
    if aux:
      aux_clauses = aux_clauses[:-1]
      aux_clauses.reverse()
      for cls in aux_clauses:
        proof_list.append((1,cls))
#        if not self.prove_no_write: self.write_clause(self.proof,cls,True)
      
#    self.write_comment(self.proof,"add and delete clauses from %d for %d" %(new_var, g_out))
    for clsID in self.variable_clauses[g_out]:
      if clsID in g_clauses: continue
      cls = self.clauses[clsID]
      new_cls = [int (v/abs(v)) * new_var if abs(v) == g_out else v for v in cls]
      g_temp = new_var
      if -new_var in new_cls:
        g_temp = -new_var
        new_cls.remove(-new_var)
      else: new_cls.remove(new_var)
      new_cls = [g_temp] + new_cls
      
      
      g_temp = g_out
      old_cls = cls[:]
      if -g_out in old_cls:
        g_temp = -g_out
        old_cls.remove(-g_out)
      else: old_cls.remove(g_out)
      old_cls = [g_temp] + old_cls
      
      
      proof_list.append((0,new_cls))
#      if not self.prove_no_write: self.write_clause(self.proof,new_cls)
      
      clause_updates.append((clsID,new_cls[:])) # cannot add them right away in case process fails
      if one_sided:
        tcls = cls[:]
        g_temp = g_out
        if -g_out in tcls:
          if -one_sided_lit != -g_out: #not actually one-sided
            self.gates_one_sided_incorrect += 1
            return False
          g_temp = -g_out
          tcls.remove(-g_out)
        else:
          if -one_sided_lit != g_out: #not actually one-sided
            self.gates_one_sided_incorrect += 1
            return False
          tcls.remove(g_out)
        tcls = [g_temp] + tcls
        delete_list.append(tcls)
      else:proof_list.append((1,old_cls))
#      if not self.prove_no_write: self.write_clause(self.proof,cls,True)
     
    
#    self.write_comment(self.proof,"delete gate for old variable %d" %(g_out))
    for clsid in g_clauses:
      cls = self.clauses[clsid]
      g_temp = g_out
      if -g_out not in cls and g_out not in cls:
        print(g_out)
        print(cls)
        print(new_var)
      
      if -g_out in cls:
        g_temp = -g_out
        cls.remove(-g_out)
      else: cls.remove(g_out)
      cls = [g_temp] + cls
      proof_list.append((1,cls[:]))
#      if not self.prove_no_write: self.write_clause(self.proof,cls,True)
      
#    self.write_comment(self.proof,"delete biconditional %d <-> %d" %(new_var, g_out))
    if bic:
      bicond2 = [-g_out, new_var] # change order fo RAT check
      proof_list.append((1,bicond1))
      proof_list.append((1,bicond2))
#      if not self.prove_no_write: self.write_clause(self.proof,bicond1, True)
#      if not self.prove_no_write: self.write_clause(self.proof,bicond2, True)
    if one_sided:
      for d in delete_list:
        proof_list.append((1,d))
      proof_list.append((1,[bicond1[1],bicond1[0]]))
      
    if not self.prove_no_write:
      for d,c in proof_list: self.write_clause(self.proof,c,d==1)
    
    # UPDATE CLAUSE DICTIONARY
    for (clsid,new_cls) in clause_updates:
      self.clauses[clsid] = new_cls
    
    self.variable_clauses[new_var] = self.variable_clauses[g_out]
    self.quantifiers[old_level][1].remove(g_out)
    self.quantifiers[max_level][1].append(new_var)
    self.variable_qlevel[new_var] = max_level
    self.var_map[g_out] = new_var
    self.var_map.append(new_var)
    self.reverse_var_map.append(g_out)

    if one_sided: self.one_sided_moves += 1

    return True

  #####################################################################################
  # GATE EQUIVALENCE
  #####################################################################################
  
  # Gate is not Eq, AND, OR
  # Need auxillary clauses to prove biconditional between old gate output
  #  and new gate output
  #
  # Use basic variable elimination technique for resolution proof, eliminating
  #   inputs until only the two gate outputs are left
  def biconditional_aux_resolvents(self, g_out, new_var, old_g_clauses, new_g_clauses, g_inputs):
    pos_old_g = [cls for cls in old_g_clauses if g_out in cls]
    neg_new_g = [cls for cls in new_g_clauses if -new_var in cls]
    clauses = pos_old_g + neg_new_g
    nclauses = len(clauses)
    active_caluses = [1] * nclauses
    variable_clauses = {}
    for idx in g_inputs + [g_out, new_var]: variable_clauses[idx] = [[],[]]
#    print(g_inputs + [g_out, new_var])
    for clsidx in range(len(clauses)):
      for l in clauses[clsidx]:
#        print(l)
        variable_clauses[abs(l)][int(l>0)].append(clsidx)
       
    aux_clauses = []
    found = False
    res_cnt = 0
    # eliminate inputs one at a time with DP var. elim. by distribution
    for g_in in g_inputs:
#      print("Eliminating %d" % (g_in))
      pos_clauses = variable_clauses[g_in][1]
      neg_clauses = variable_clauses[g_in][0]
#      print(pos_clauses)
#      print(neg_clauses)
      for p_clause in pos_clauses:
        if not active_caluses[p_clause]: continue
        p_lits = clauses[p_clause]
        for n_clause in neg_clauses:
          if not active_caluses[n_clause]: continue
          n_lits = clauses[n_clause]
#          print("RESOLVING")
#          print(p_lits)
#          print(n_lits)
          resolventT = p_lits + n_lits
          resolventT.remove(g_in)
          resolventT.remove(-g_in)
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
            nclauses += 1
            if resolvent == [g_out, -new_var]:
              found = True
              break
        if found: break
      for clsid in pos_clauses + neg_clauses:
        active_caluses[clsid] = 0
      if found: break
    
#    for clsidx in range(nclauses):
#      if active_caluses[clsidx]:
#        print(clauses[clsidx])
#    print(active_caluses)
    return aux_clauses
  
  
  #######################################################################################
  # WRITING AND MISCL. FUNCTIONS
  #######################################################################################
  
  def write_qbf(self, fname):
    file = open(fname, 'w')
    file.write("c Statistics\n")
    file.write("c Number of gates: "+str(self.ngates))
    file.write("\nc Number of gates moved: "+str(self.ngates_moved))
    file.write("\nc Number of gates incorrect: "+str(self.ngates_incorrect))
    
    file.write("\n\np cnf %d %d\n" % (self.nvar, self.ncls))
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


  # -- Gate output --
  # Written in order from inputs to outputs
  # for each gate,
  # GateInputs:
  # GateInputTseitens:
  # GateOutput:
  def write_gates(self, fname):
    file = open(fname, 'w')
    init_gates = self.initial_gates()
    seen = [0] * (self.nvar+1) # gate output seen in bfs
    support = {}
    q = Queue()
    for gidx in init_gates: q.put(gidx)
    # BFS across gates, following input to output ordering
    while not q.empty():
      gidx = q.get()
      g = self.gates[gidx]
      g_outlit = g.outlit
      g_out = abs(g_outlit)
      g_inputs = g.inputs
      variables = g_inputs + [g_out]
      if seen[g_out]: continue
      # check other inputs
      if any([not seen[v] for v in g_inputs if self.is_gate_out[v]]):
        continue # other input gates need to be processed (seen) first
      seen[g_out] = 1 # gate has been processed
      # add new gates where g_out is input
      if g_out in self.variable_g_in:
        for ng in self.variable_g_in[g_out]: q.put(ng)
      # Move in qnf
      self.write_gate(gidx, file)
  
  def write_gate(self,gidx,file):
    g = self.gates[gidx]
    g_outlit = g.outlit
    g_out = abs(g_outlit)
    g_inputs = g.inputs
    ilist = g_inputs
    slist = [str(i) for i in ilist]
    istring = " ".join(slist)
    file.write("GateInputs: " + istring + "\n")
    tseitens = [v for v in g_inputs if self.is_gate_out[v]]
    ilist = tseitens
    slist = [str(i) for i in ilist]
    istring = " ".join(slist)
    file.write("GateInputTseitens: "+ istring + "\n")
    file.write("GateOutput: %d\n\n" % (g_outlit))
  
  def write_comment(self, file, comment):
    file.write("c "+comment+"\n")
    
  def write_clause(self, file, clause, delete = False):
    ilist = clause + [0]
    slist = [str(i) for i in ilist]
    if delete : slist = ['d'] + slist
    istring = " ".join(slist)
    file.write(istring + '\n')
  def print_stats(self):
    print("Statistics")
    print("Number of gates: "+str(self.ngates))
    print("Number of XORs and Semantic: "+str(self.nxor_gates))
    print("Number of gates moved: "+str(self.ngates_moved))
    print("Number of gates incorrect out of order: "+str(self.gates_out_of_order))
    print("Number of gates incorrect on universal: "+str(self.gates_on_universal))
    print("Number of gates incorrect not defined: "+str(self.gates_notdefined))
    print("Number of gates incorrect one-sided: "+str(self.gates_one_sided_incorrect))
    if self.ngates_moved > 0:
      print("Total difference in levels for moved variables: "+str(self.total_nlevels_moved))
      print("Average difference in levels for moved variables: "+str(self.total_nlevels_moved/self.ngates_moved))
      print("One-sided moves: "+str(self.one_sided_moves))
      print("Explicit XOR moves: "+str(self.nxor_moved))
      print("Semantic moves: "+str(self.nsemantic_moved))
  
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
    gateName = None
    outqbfName = None
    outgateName = None
    proofName = None
    prove_no_write = False
    xor_processing = False
    move_gates = False
    restrictGates = False
    verbosity = 0
    var_map_name = None
    pseudo = False
    
    optlist, args = getopt.getopt(args, "swhdrxmv:q:o:g:l:p:b:")
    for (opt, val) in optlist:
        if opt == '-h':
          usage(name)
          return
        elif opt == '-q':
          qbfName = val
        elif opt == '-g':
          gateName = val
        elif opt == '-o':
          outqbfName = val
        elif opt == '-b':
          var_map_name = val
        elif opt == '-l':
          outgateName = val
        elif opt == '-p':
          proofName = val
        elif opt == '-x':
          xor_processing = True
        elif opt == '-m':
          move_gates = True
        elif opt == '-v':
          verbosity = int(val)
        elif opt == '-w':
          prove_no_write = True
        elif opt == '-r':
          restrictGates = True
        elif opt == '-s':
          pseudo = True
    
#    print(qbfName)
    qbf = QBF_Gate_Processor(qbfName, proofName, verbosity, prove_no_write,restrictGates, pseudo)
    
    qbf.read_gates(gateName)
    
#    if xor_processing:
##      print("Start processing xors")
#      qbf.process_XOR_outputs()
##      print("Endt processing xors")
##      print("Start processing dangling eqs")
#      qbf.process_dangling_equivalances()
##      print("End processing dangling eqs")

    if move_gates:
#      print("Start moving variables")
      qbf.move_by_level()
#      print("End moving variables")
    
    if not outqbfName is None:
      qbf.write_qbf(outqbfName)
    
    if not outgateName is None:
      qbf.write_gates(outgateName)
    
    if not var_map_name is None:
      qbf.print_var_map(var_map_name)
    
    qbf.print_stats()
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
