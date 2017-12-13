#!/usr/bin/env python3
# --------------------
import sys, os
if os.path.exists("/Users/admin/Projects/ToevScript"):
    sys.path.insert(0, "/Users/admin/Projects/ToevScript")
else:
    sys.path.insert(0, "/home/mrcoco/Devel/ToevScript")
# --------------------
from toevscript import io
from toevscript import core
from toevscript import evaluator
from toevscript import grapher
# --------------------
# Graphers
# --------------------
def reposit(pdata, r0, r1, glim):
    if r0 not in pdata and 1 not in pdata:
        return -1
    if r0 not in pdata:
        return -1
    if r1 not in pdata:
        return -1

    csp  = False
    gpid = False

    if 'potential-primes' in pdata[r1] and int(pdata[r1]['potential-primes'][0]) > 0:
        csp  = True
    if 'primes' in pdata[r1] and int(pdata[r1]['primes'][0]) > 0:
        csp  = True
    if 'implicates' in pdata[r0] and int(pdata[r0]['implicates'][0]) > glim:
        gpid = True

    if csp:
        return 1
    if gpid:
        return 2
    return 3
# --------------------
#Grapher01 = grapher.ProblemCatSplitter(lambda x : reposit(x, 2, 3, 0), { 1:'cSP @gtime First', 2:'GPiD First', 3:'No First' }, title='Size 1 Who gives the first implicate in 15"')
#Grapher02 = grapher.ProblemCatSplitter(lambda x : reposit(x, 2, 3, 1), { 1:'cSP @gtime First', 2:'GPiD First', 3:'No First' }, title='Size 1 Who gives the first implicate in 15" w/strict')
#Grapher04 = grapher.ProblemCatSplitter(lambda x : reposit(x, 2, 4, 1), { 1:'cSP @ttime First', 2:'GPiD First', 3:'No First' }, title='Size 1 Who gives the first implicate in 15" w/strict')
# --------------------
Grapher03 = grapher.ProblemCatSplitter(lambda x : reposit(x, 2, 4, 0), { 1:'cSP @ttime First', 2:'GPiD First', 3:'No First' }, title='Size 1 Who gives the first implicate in 15"')
# --------------------
# Script
# --------------------
script = core.ScriptBox()

script.add_command(core.ImportContextCommand(sys.argv[1]))

#script.add_command(core.GraphCommand('problems', Grapher01, 'wf-01.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher02, 'wf-02.pdf'))
script.add_command(core.GraphCommand('problems', Grapher03, 'wf-03.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher04, 'wf-04.pdf'))

script.execute()
# --------------------
