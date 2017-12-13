#!/usr/bin/env python3
# --------------------
import sys, os
import statistics as stat
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
StrictTimeFilter101 = grapher.ProblemFilter('&101.gtime', lambda x : float(x) > 15)
StrictTimeFilter102 = grapher.ProblemFilter('&102.gtime', lambda x : float(x) > 15)
StrictTimeFilter103 = grapher.ProblemFilter('&103.gtime', lambda x : float(x) > 15)
StrictTimeFilter104 = grapher.ProblemFilter('&104.gtime', lambda x : float(x) > 15)
ExistFilter101 = grapher.ProblemFilter('&101.implicates', lambda x : int(x) < 1)
ExistFilter102 = grapher.ProblemFilter('&102.implicates', lambda x : int(x) < 1)
ExistFilter103 = grapher.ProblemFilter('&103.implicates', lambda x : int(x) < 1)
ExistFilter104 = grapher.ProblemFilter('&104.implicates', lambda x : int(x) < 1)
OutOfClassFilter101 = grapher.ProblemMultiFilter(['&101.implicates', '&101.gtime'],
                                                 lambda l : int(l[0]) == 1 and float(l[1]) > 15)
OutOfClassFilter103 = grapher.ProblemMultiFilter(['&103.implicates', '&103.gtime'],
                                                 lambda l : int(l[0]) == 1 and float(l[1]) > 15)
# --------------------
Grapher01 = grapher.SerieHistogram('&101.implicates', int,
                                   filters=[ExistFilter101, OutOfClassFilter101],
                                   title='Generation of implicates of size 1 in 15"',
                                   xlabel='Number of implicates generated',
                                   ylabel='Number of examples')
Grapher02 = grapher.SerieHistogram('&103.implicates', int,
                                   filters=[ExistFilter103, OutOfClassFilter103],
                                   title='Generation of implicates of any size in 15"',
                                   xlabel='Number of implicates generated',
                                   ylabel='Number of examples')
Grapher03 = grapher.SerieHistogram('&102.gtime', float,
                                   filters=[StrictTimeFilter102, ExistFilter102],
                                   title='Generation of one implicate of size 1',
                                   xlabel='Time (in seconds) necessary to generate one implicate',
                                   ylabel='Number of examples')
Grapher04 = grapher.SerieHistogram('&104.gtime', float,
                                   filters=[StrictTimeFilter104, ExistFilter104],
                                   title='Generation of one implicate of any size',
                                   xlabel='Time (in seconds) necessary to generate one implicate',
                                   ylabel='Number of examples')
# --------------------
def gen_GPiD_AL1Ex(ref):
    def local_f(pdata):
        val = 0
        try:
            icount = pdata.get_reference('&{ev}.implicates'.format(ev=ref))
            gtime  = pdata.get_reference('&{ev}.gtime'.format(ev=ref))
            if float(gtime) > 15:
                val = max(int(icount) - 1, 0)
            else:
                val = int(icount)
        except core.UndefinedEvaluationResultException:
            pass
        return True if val > 0 else None
    return local_f
# --------------------
def gen_GPiD_AGEx(ref):
    def local_f(pdata):
        try:
            gtime  = pdata.get_reference('&{ev}.gtime'.format(ev=ref))
            if float(gtime) < 14.9:
                return True
            else:
                return None
        except core.UndefinedEvaluationResultException:
            return None
    return local_f
# --------------------
def gen_GPiD_TimeU15Ex(ref):
    def local_f(pdata):
        try:
            gtime  = pdata.get_reference('&{ev}.gtime'.format(ev=ref))
            if float(gtime) > 15:
                return None
            else:
                return float(gtime)
        except core.UndefinedEvaluationResultException:
            return None
    return local_f
# --------------------
Vx01 = grapher.ValueXtractor('0 GPiD Examples size 1', gen_GPiD_AL1Ex(101), lambda x : 1 - len(x)/400)
Vx02 = grapher.ValueXtractor('0 GPiD Examples size ?', gen_GPiD_AL1Ex(103), lambda x : 1 - len(x)/400)

#Vx03 = grapher.ValueXtractor('All generated GPiD Examples size 1', gen_GPiD_AGEx(0), lambda x : len(x)/2549)
#Vx04 = grapher.ValueXtractor('All generated GPiD Examples size 1', gen_GPiD_AGEx(5), lambda x : len(x)/2549)

Vx05 = grapher.ValueXtractor('Mean 1st S1 implicate gen-time u15', gen_GPiD_TimeU15Ex(102), stat.mean)
Vx06 = grapher.ValueXtractor('Mean 1st S? implicate gen-time u15', gen_GPiD_TimeU15Ex(104), stat.mean)
Vx07 = grapher.ValueXtractor('Median 1st S1 implicate gen-time u15', gen_GPiD_TimeU15Ex(102), stat.median)
Vx08 = grapher.ValueXtractor('Median 1st S? implicate gen-time u15', gen_GPiD_TimeU15Ex(104), stat.median)

Vx101 = grapher.ValueXtractor('Prop S1 1st generated under 0.05', gen_GPiD_TimeU15Ex(102),
                                  lambda x : len([l for l in x if l < 0.05])/400)
Vx102 = grapher.ValueXtractor('Prop S? 1st generated under 0.05', gen_GPiD_TimeU15Ex(104),
                                  lambda x : len([l for l in x if l < 0.05])/400)
Vx103 = grapher.ValueXtractor('Prop S1 1st generated under 0.1', gen_GPiD_TimeU15Ex(102),
                                  lambda x : len([l for l in x if l < 0.1])/400)
Vx104 = grapher.ValueXtractor('Prop S? 1st generated under 0.1', gen_GPiD_TimeU15Ex(104),
                                  lambda x : len([l for l in x if l < 0.1])/400)
Vx105 = grapher.ValueXtractor('Prop S1 1st generated under 0.5', gen_GPiD_TimeU15Ex(102),
                                  lambda x : len([l for l in x if l < 0.5])/400)
Vx106 = grapher.ValueXtractor('Prop S? 1st generated under 0.5', gen_GPiD_TimeU15Ex(104),
                                  lambda x : len([l for l in x if l < 0.5])/400)
Vx107 = grapher.ValueXtractor('Prop S1 1st generated under 1', gen_GPiD_TimeU15Ex(102),
                                  lambda x : len([l for l in x if l < 1])/400)
Vx108 = grapher.ValueXtractor('Prop S? 1st generated under 1', gen_GPiD_TimeU15Ex(104),
                                  lambda x : len([l for l in x if l < 1])/400)
Vx109 = grapher.ValueXtractor('Prop S1 1st generated under 5', gen_GPiD_TimeU15Ex(102),
                                  lambda x : len([l for l in x if l < 5])/400)
Vx110 = grapher.ValueXtractor('Prop S? 1st generated under 5', gen_GPiD_TimeU15Ex(104),
                                  lambda x : len([l for l in x if l < 5])/400)

# --------------------
# Script
# --------------------
script = core.ScriptBox()

script.add_command(core.ImportContextCommand(sys.argv[1]))

script.add_command(core.GraphCommand('qf-uflia', Grapher01, 'qf-uflia-01.pdf'))
script.add_command(core.GraphCommand('qf-uflia', Grapher02, 'qf-uflia-02.pdf'))
script.add_command(core.GraphCommand('qf-uflia', Grapher03, 'qf-uflia-03.pdf'))
script.add_command(core.GraphCommand('qf-uflia', Grapher04, 'qf-uflia-04.pdf'))

script.add_command(core.ExtractCommand('qf-uflia', Vx01))
script.add_command(core.ExtractCommand('qf-uflia', Vx02))

script.add_command(core.ExtractCommand('qf-uflia', Vx05))
script.add_command(core.ExtractCommand('qf-uflia', Vx06))
script.add_command(core.ExtractCommand('qf-uflia', Vx07))
script.add_command(core.ExtractCommand('qf-uflia', Vx08))

script.add_command(core.ExtractCommand('qf-uflia', Vx101))
script.add_command(core.ExtractCommand('qf-uflia', Vx102))
script.add_command(core.ExtractCommand('qf-uflia', Vx103))
script.add_command(core.ExtractCommand('qf-uflia', Vx104))
script.add_command(core.ExtractCommand('qf-uflia', Vx105))
script.add_command(core.ExtractCommand('qf-uflia', Vx106))
script.add_command(core.ExtractCommand('qf-uflia', Vx107))
script.add_command(core.ExtractCommand('qf-uflia', Vx108))
script.add_command(core.ExtractCommand('qf-uflia', Vx109))
script.add_command(core.ExtractCommand('qf-uflia', Vx110))

script.execute()
# --------------------
