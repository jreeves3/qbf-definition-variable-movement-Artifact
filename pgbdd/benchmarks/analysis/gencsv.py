#!/usr/bin/python

# Extract file name and numbers from file generated by grep
# Sample input
# chess-064-column.data:Node 553552.  Size = 1055, Solutions = 860778005594247069. After quantification for column 62

# Want to find file name + anything that looks like a number
# Also, try to extract number out of file name
# print fname,fnumber,val1,...,valK


import sys

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

def getFile(line):
    fields = line.split(":")
    if len(fields) == 1:
        return None
    fname = fields[0]
    subname = fname.split()
    if len(subname) > 1:
        return None
    return fname

def findNumber(name):
    found = False
    val = 0
    for c in name:
        if c >= '0' and c <= '9':
            val = 10 * val + (ord(c) - ord('0'))
            found = True
        else:
            if found:
                break
    return val if found else None
    

def getNumbers(line):
    fields = line.split()
    vals = []
    for field in fields:
        if field[-1] in ",.":
            field = field[:-1]
        success = None
        val = None
        try:
            val = int(field)
            success = True
        except:
            pass
        if not success:
            try:
                val = float(field)
                success = True
            except:
                pass
        if success:
            vals.append(val)
    return vals


for line in sys.stdin:
    line = trim(line)
    fields = []
    fname = getFile(line)
    if fname is not None:
        fields.append(fname)
        fval = findNumber(fname)
        if fval is not None:
            fields.append(str(fval))

    vals = getNumbers(line)
    for v in vals:
        fields.append(str(v))

    if len(fields) > 0:
        sys.stdout.write(",".join(fields) + "\n")
