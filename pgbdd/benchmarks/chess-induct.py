#!/usr/bin/python

import sys
import  getopt
import writer


# Generate files for N x * mutilated chessboard problem,
# Showing there are no solutions for N x M for all values of M > 1
def usage(name):
    print("Usage: %s [-h] [-c] [-f] [-v] [-r ROOT] -n N [-m M]" % name) 
    print("  -h       Print this message")
    print("  -v       Run in verbose mode")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf, ROOT.order, and ROOT.schedule")
    print("  -c       Include corners (i.e., don't mutilate)")
    print("  -n N     Specify number of rows in board")
    print("  -m M     Specify number of columns in board (if different)")
    print("  -f       Perform fixed-point check, ascertaining that Configs(M-1) == Configs(M-3)")


def popcount(x):
    count = 0
    while x != 0:
        count += x & 1
        x = x >> 1
    return count

def bitList(x, count):
    ls = []
    for i in range(count):
        b = (x>>i) & 1
        ls.append(b)
    return ls

# Less efficient version
def exactlyOneOld(vars):
    n = len(vars)
    if n == 0:
        return None # Can't do it
    # Generate integer values for not = 1
    bits = []
    for x in range(1<<n):
        if popcount(x) != 1:
            bits.append(bitList(x, n))
    # Build clauses, inverting bits
    clauses = []
    for blist in bits:
        clause = [vars[i] if blist[i] == 0 else -vars[i] for i in range(n)]
        clauses.append(clause)
    return clauses

def exactlyOne(vars):
    n = len(vars)
    if n == 0:
        return None # Can't do it
    # At least one
    clauses = [vars]
    # at most one via pairwise constraints
    for i in range(n):
        for j in range(i):
            clause = [-vars[i], -vars[j]]
            clauses.append(clause)
    return clauses


# Numbering scheme:
# Columns numbered from 0 to N-1
# Rows numbered from 0 to N-1
# H(r,c) denotes horizontal divider between rows r-1 and r for column c
#   Range: r: 1..n-1.  c:0..n-1
# V(r,c) denotes vertical divider between columns c-1 and c for row r
#   Range: r: 0..n-1,  c:1..n-1


# Square at position r,c has
# top divider at r,c
# bottom dividerr at r+1,c
# left divider at r,c
# right divider at r,c+1

class Square:
    top = None
    right = None
    bottom = None
    left = None
    row = 0
    col = 0
    categoryName = "square"

    # idDict: Dictionary of variable identifiers, indexed by (row, col, isHorizontal)
    def __init__(self, row, col, idDict):
        self.row = row
        self.col = col
        
        if (row,col,True) in idDict:
            self.top = idDict[(row,col,True)]
        else:
            self.top = None
        if (row+1,col,True) in idDict:
            self.bottom = idDict[(row+1,col,True)]
        else:
            self.bottom = None

        if (row,col,False) in idDict:
            self.left = idDict[(row,col,False)]
        else:
            self.left = None
        if (row,col+1,False) in idDict:
            self.right = idDict[(row,col+1,False)]
        else:
            self.right = None

    def doClauses(self, writer):
        allVars = [self.top, self.right, self.bottom, self.left]
        vars = [v for v in allVars if v is not None]
        clist = []
        if len(vars) > 1:  # Not chopped corner
            writer.doComment("Exactly one constraints for %s %d,%d (%d variables)" % (self.categoryName, self.row, self.col, len(vars)))
            clauses = exactlyOne(vars)
            for clause in clauses:
                clist.append(writer.doClause(clause))
        return clist

# Like a square, but "right" divider jumps back to column c-1
# This allows testing for convergence
class ReverseSquare(Square):
    def __init__(self, row, col, idDict):
        Square.__init__(self, row, col, idDict)
        # Redefine rightmost variable
        if (row,col-1,False) in idDict:
            self.right = idDict[(row,col-1,False)]
        else:
            self.right = None
        self.categoryName = "reverse square"
        


# Extension of original version to explicitly include number of columns as separate value
class Board:
    # Variable ids, indexed by (row, col, isHorizontal)
    idDict = {}
    # Squares indexed by (row, col)
    squares = {}
    variableCount = 0
    cnfWriter = None
    scheduleWriter = None
    orderWriter = None
    verbose = False
    includeCorners = False
    n = None  # Number of rows
    m = None  # Number of columns
    # What approach should be used to construct board
    doLinear = True
    # Am I trying to prove convergence?
    fixedPoint = False

    def __init__(self, n, rootName, verbose = False, includeCorners = False, m = None, fixedPoint = False):
        self.n = n
        self.m = self.n if m is None else m
        self.fixedPoint = fixedPoint
        variableCount = self.m * (self.n-1) + self.n * (self.m-1)
        if not includeCorners:
            if self.fixedPoint:
                variableCount -= 2
            else:
                variableCount -= 4
        self.verbose = verbose
        self.includeCorners = includeCorners
        self.cnfWriter = writer.CnfWriter(variableCount, rootName, self.verbose)
        self.scheduleWriter = writer.ScheduleWriter(variableCount, rootName, self.verbose)
        self.orderWriter = writer.OrderWriter(variableCount, rootName, self.verbose)
        self.idDict = {}
        self.squares = {}
        self.variableCount = 0

    def nextVariable(self):
        self.variableCount += 1
        return self.variableCount

    # Construct Column i.  Return lists of variables on left and right
    def doColumn(self, c):
        left = []
        right = []
        quants = []
        self.scheduleWriter.doComment("Adding column %d" % c)
        # Has something been put onto the stack?
        gotValue = False
        for ir in range(self.n):
            r = self.n-ir-1
            sq = self.squares[(r,c)]
            clist = sq.doClauses(self.cnfWriter)
            if len(clist) > 0:
                self.scheduleWriter.getClauses(clist)
                count = len(clist) if gotValue else len(clist)-1
                if count > 0:
                    self.scheduleWriter.doAnd(count)
                    gotValue = True
            if sq.bottom is not None:
                quants.append(sq.bottom)
            if sq.left is not None:
                left.append(sq.left)
            if sq.right is not None:
                right.append(sq.right)
        if len(quants) > 0:
            self.scheduleWriter.doQuantify(quants)
        self.scheduleWriter.doComment("Completed column %d.  Quantified %d variables" % (c, len(quants)))
        return (left, right)


    def storeName(self):
        c = self.m-3
        return"C%d" % c

    def constructBoard(self):
        sname = self.storeName()
        # Combine columns from left to right
        for c in range(self.m):
            (left, right) = self.doColumn(c)
            if c > 0:
                self.scheduleWriter.doComment("Combine column %d with predecessors" % c)
                self.scheduleWriter.doAnd(1)
                if len(left) > 0:
                    self.scheduleWriter.doQuantify(left)
            self.scheduleWriter.doInformation("After quantification for column %d" % c)
            if self.fixedPoint and c == self.m-3:
                self.scheduleWriter.doComment("Storing result from column %d" % c)
                self.scheduleWriter.doStore(sname)
        if self.fixedPoint:
            # Check for convergence
            self.scheduleWriter.doRetrieve(sname)
            self.scheduleWriter.doEquality()

    # Complete last two columns with mutilated board
    def constructBoardLast2(self):
        sname = self.storeName()
        self.scheduleWriter.doRetrieve(sname)
        n = self.n
        m = self.m
        # Combine columns from left to right
        for c in range(m-2,m):
            (left, right) = self.doColumn(c)
            self.scheduleWriter.doComment("Combine mutilated column %d with predecessors" % c)
            self.scheduleWriter.doAnd(1)
            if len(left) > 0:
                self.scheduleWriter.doQuantify(left)
            self.scheduleWriter.doInformation("After quantification for mutilated column %d" % c)
        self.scheduleWriter.doDelete(sname)
            

    def build(self):
        n = self.n
        m = self.m
        # Generate variables
        for r in range(n):
            if r >= 1:
                hlist = []
                for c in range(m):
                    # Horizontal divider above.  Omit ones for UL and LR corners
                    omit = not self.includeCorners and (r==1 and c ==0)
                    if not self.fixedPoint:
                        omit = omit or not self.includeCorners and (r==n-1 and c==m-1)
                    if not omit:
                        v = self.nextVariable()
                        self.idDict[(r,c,True)] = v
                        hlist.append(v)
                self.orderWriter.doOrder(hlist)

            vlist = []
            for c in range(1, m):
                # Vertical divider to left.  Omit ones for UL and LR corners
                omit = not self.includeCorners and (r==0 and c ==1)
                if not self.fixedPoint:
                    omit = omit or not self.includeCorners and (r==n-1 and c==m-1)
                if not omit:
                    v = self.nextVariable()
                    self.idDict[(r,c,False)] = v
                    vlist.append(v)
            self.orderWriter.doOrder(vlist)

        # Generate squares
        for r in range(n):
            for c in range(m):
                self.squares[(r,c)] = ReverseSquare(r, c, self.idDict) if self.fixedPoint and c == m-1 else Square(r, c, self.idDict)
        self.constructBoard()

    # Construct mutilated version of last two columns
    def buildLast2(self):
        n = self.n
        m = self.m
        # Remove corner variables
        del self.idDict[(n-1,m-1,False)]
        del self.idDict[(n-1,m-1,True)]
        # Rebuild two squares in lower, righthand corner
        for r in range(n):
            for c in range(m-2, m):
                self.squares[(r,c)] = Square(r, c, self.idDict)

        self.constructBoardLast2()

    def finish(self):
        self.cnfWriter.finish()
        self.orderWriter.finish()
        self.scheduleWriter.finish()
                           
def run(name, args):
    verbose = False
    n = 0
    m = None
    rootName = None
    includeCorners = False
    fixedPoint = False
    
    optlist, args = getopt.getopt(args, "hvcar:n:m:f")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-c':
            includeCorners = True
        elif opt == '-r':
            rootName = val
        elif opt == '-n':
            n = int(val)
        elif opt == '-m':
            m = int(val)
        elif opt == '-f':
            fixedPoint = True
        
    if n == 0:
        print("Must have value for n")
        usage(name)
        return
    if rootName is None:
        print("Must have root name")
        usage(name)
        return
    b = Board(n, rootName, verbose, includeCorners, m = m, fixedPoint = fixedPoint)
    b.build()
    if fixedPoint:
        b.buildLast2()
    b.finish()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

