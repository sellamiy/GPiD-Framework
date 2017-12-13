#!/usr/bin/env python3
# --------------------
import sys, os
import statistics as stat
if os.path.exists("/Users/admin/Projects/ToevScript"):
    sys.path.insert(0, "/Users/admin/Projects/ToevScript")
else:
    sys.path.insert(0, "/home/mrcoco/Devel/ToevScript")
# --------------------
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
# --------------------
from toevscript import io
from toevscript import core
from toevscript import evaluator
from toevscript import grapher
# --------------------
# Graphers
# --------------------
def StrictTimeFilter(serie, time, sname='gtime'):
    return grapher.ProblemFilter('&{s}.{n}'.format(s=serie, n=sname), lambda x : float(x) > time)
def ExistFilter(serie, sname='implicates'):
    return grapher.ProblemFilter('&{s}.{n}'.format(s=serie, n=sname), lambda x : int(x) < 1)
def OutOfClassFilter(serie, time, tsname='gtime', isname='implicates'):
    return grapher.ProblemMultiFilter(['&{s}.{n}'.format(s=serie, n=isname),
                                       '&{s}.{n}'.format(s=serie, n=tsname)],
                                       lambda l : int(l[0]) == 1 and float(l[1]) > time)
# --------------------
# ------- From YET TO EXECUTE benchmark data
# Time for gpid first in QF_UF
Grapher01 = grapher.MultiSerieHistogramAsTable(
    ['&{s}.gtime'.format(s=i) for i in (3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008)],
    [int] * 8,
    2549,
    ['Maximal size = {i}'.format(i=i) for i in (1,2,3,4,5,6,7,8)] + ['Maximal size not limited'],
    filters=[], # TODO: Add to modifier to put excluded examples into the last class
    title='',
    xlabel='Time (in seconds) necessary to generate at least one implicate - last category: more than 10"',
    ylabel='Number of examples'
    )
# ------- From YET TO EXECUTE benchmark data
# Time for gpid first in QF_UFLIA
Grapher02 = grapher.MultiSerieHistogramAsTable(
    ['&{s}.gtime'.format(s=i) for i in (4001, 4002, 4003, 4004, 4005, 4006, 4007, 4008)],
    [int] * 8,
    400,
    ['Maximal size = {i}'.format(i=i) for i in (1,2,3,4,5,6,7,8)] + ['Maximal size not limited'],
    filters=[], # TODO: Add to modifier to put excluded examples into the last class
    title='',
    xlabel='Time (in seconds) necessary to generate at least one implicate - last category: more than 10"',
    ylabel='Number of examples'
    )
# ------- From SizeLoop
# QFUF
def ImplicateExists(ref):
    def local_f(pdata):
        try:
            icount = pdata.get_reference('&{ev}.implicates'.format(ev=ref))
            return True if int(icount) > 0 else None
        except core.UndefinedEvaluationResultException:
            return None
    return local_f
# # # # # # # #
def ImplicateExistsAndNonCspBroken(ref, rcsp):
    def local_f(pdata):
        try:
            pdata.get_reference('&{ev}.broken'.format(ev=rcsp))
            return None
        except core.UndefinedEvaluationResultException:
            pass
        try:
            icount = pdata.get_reference('&{ev}.implicates'.format(ev=ref))
            return True if int(icount) > 0 else None
        except core.UndefinedEvaluationResultException:
            return None
    return local_f
# # # # # # # #
result_getters_uf = []
for size in range(1, 9):
    Vx = grapher.ValueXtractor('', ImplicateExists(3000+size), lambda x : 100 * len(x)/2549)
    result_getters_uf.append(Vx)
# QFLIA - YET TO RUN
result_getters_uflia = []
for size in range(1, 9):
    Vx = grapher.ValueXtractor('', ImplicateExists(4000+size), lambda x : 100 * len(x)/400)
    result_getters_uflia.append(Vx)
# ------- From DimTo
result_getters_both_gpid = []
result_getters_both_csp = []
for timeout in (3, 5, 10):
    Vx_G =  grapher.ValueXtractor('', ImplicateExists(400+timeout), lambda x : 100 * len(x)/337)
    Vx_C =  grapher.ValueXtractor('', ImplicateExists(500+timeout), lambda x : 100 * len(x)/337)
    result_getters_both_gpid.append(Vx_G)
    result_getters_both_csp.append(Vx_C)
Vx_G =  grapher.ValueXtractor('', ImplicateExistsAndNonCspBroken(5, 6), lambda x : 100 * len(x)/337)
Vx_C =  grapher.ValueXtractor('', ImplicateExistsAndNonCspBroken(6, 6), lambda x : 100 * len(x)/337)
result_getters_both_gpid.append(Vx_G)
result_getters_both_csp.append(Vx_C)
# Othd
result_getters_isz_gpid = []
result_getters_isz_csp = []
for size in range(1, 16):
    Vx_G =  grapher.ValueXtractor('', ImplicateExists(1000+size), lambda x : 100 * len(x)/337)
    Vx_C =  grapher.ValueXtractor('', ImplicateExists(2000+size), lambda x : 100 * len(x)/337)
    result_getters_isz_gpid.append(Vx_G)
    result_getters_isz_csp.append(Vx_C)
# # # # # # # #
# --------------------
# Script
# --------------------
script = core.ScriptBox()

dimto = sys.argv[1]
loop  = sys.argv[2]

first = sys.argv[3] # TODO
mrefs = sys.argv[4] # TODO
mrefa = sys.argv[5] # TODO

dimt2 = sys.argv[6]
#lialoop = sys.argv[4] # TODO

script.add_command(core.ImportContextCommand(dimto,   'problems', [403, 405, 410, 503, 505, 510]))
script.add_command(core.ImportContextCommand(dimt2,   'problems', [403, 405]))
script.add_command(core.ImportContextCommand(loop,    'problems', [1000 + i for i in range(1, 16)]))
script.add_command(core.ImportContextCommand(loop,    'problems', [2000 + i for i in range(1, 16)]))
script.add_command(core.ImportContextCommand(first,   'problems', [3000 + i for i in (1,2,3,4,5,6,7,8)]))
script.add_command(core.ImportContextCommand(first,   'qf-uflia', [4000 + i for i in (1,2,3,4,5,6,7,8)]))
script.add_command(core.ImportContextCommand(mrefs,   'problems', [5]))
script.add_command(core.ImportContextCommand(mrefa,   'problems', [6]))
#script.add_command(core.ImportContextCommand(lialoop, 'qf-uflia', [2000 + i for i in range(1, 16)]))

script.add_command(core.GraphCommand('problems', Grapher01, 'histo_01.txt'))
script.add_command(core.GraphCommand('qf-uflia', Grapher02, 'histo_02.txt'))

script.execute()

results_uf        = [ Vx.extract(script.context['problems']) for Vx in result_getters_uf        ]
results_uflia     = [ Vx.extract(script.context['qf-uflia']) for Vx in result_getters_uflia     ]
results_both_gpid = [ Vx.extract(script.context['problems']) for Vx in result_getters_both_gpid ]
results_both_csp  = [ Vx.extract(script.context['problems']) for Vx in result_getters_both_csp  ]
results_isz_gpid = [ Vx.extract(script.context['problems']) for Vx in result_getters_isz_gpid ]
results_isz_csp  = [ Vx.extract(script.context['problems']) for Vx in result_getters_isz_csp  ]

figure, ax = plt.subplots()
figure.suptitle('')
ax.set_xlabel('Maximal implicate size (literal count)')
ax.set_ylabel('Proportion of examples')
ax.bar(range(1, 9), results_uf)

grapher.exportFigure(figure, 'histo_03.pdf')

figure, ax = plt.subplots()
figure.suptitle('')
ax.set_xlabel('Maximal implicate size (literal count)')
ax.set_ylabel('Proportion of examples')
ax.bar(range(1, 9), results_uflia)

grapher.exportFigure(figure, 'histo_04.pdf')

figure, ax = plt.subplots()
figure.suptitle('')
ax.set_xlabel('Timeout (in seconds)')
ax.set_ylabel('Proportion of examples')
ax.bar(('03','05','10','15'), results_both_gpid, width=0.4, color='xkcd:deep blue')
ax.bar(('03','05','10','15'), results_both_csp, align='edge', width=0.4, color='xkcd:yellow orange')

grapher.exportFigure(figure, 'histo_05.pdf')

figure, ax = plt.subplots()
figure.suptitle('')
ax.set_xlabel('Maximal implicate size allowed')
ax.set_ylabel('Proportion of examples')
ax.bar(range(1,16), results_isz_gpid, width=0.4, color='xkcd:deep blue')
ax.bar(range(1,16), results_isz_csp, align='edge', width=0.4, color='xkcd:yellow orange')

grapher.exportFigure(figure, 'histo_06.pdf')

# --------------------
