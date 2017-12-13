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
Grapher02 = grapher.SerieCompareGrapher('&0.implicates', '&1.potential-primes', int, int,
                                        title='Number of implicates of size 1 generated in 15"',
                                        xlabel='gpid-gts-z3', ylabel='csp.native @potential-primes')
Grapher08 = grapher.SerieCompareGrapher('&5.implicates', '&6.implicates', int, int,
                                        title='Number of implicates of any size generated in 15"',
                                        xlabel='gpid-gts-z3', ylabel='csp.native @implicates',
                                        logscale=True)
# --------------------
#Grapher01 = grapher.SerieCompareGrapher('&0.implicates', '&1.implicates', int, int, title='Number of implicates of size 1 generated in 15"', xlabel='gpid-gts-z3', ylabel='csp.native @implicates')
#Grapher03 = grapher.SerieCompareGrapher('&0.implicates', '&1.primes', int, int, title='Number of implicates of size 1 generated in 15"', xlabel='gpid-gts-z3', ylabel='csp.native @primes')
#Grapher04 = grapher.SerieCompareGrapher('&0.gtime', '&1.etime', float, float, title='Seconds of exec comparisons for size 1 generation to 15"', xlabel='gpid-gts-z3 @generation', ylabel='csp.native @execution')
#Grapher05 = grapher.SerieCompareGrapher('&0.gtime', '&1.itime', float, float, title='Seconds of exec comparisons for size 1 generation to 15"', xlabel='gpid-gts-z3 @generation', ylabel='csp.native @interrupt')
#Grapher06 = grapher.SerieCompareGrapher('&0.ttime', '&1.etime', float, float, title='Seconds of exec comparisons for size 1 generation to 15"', xlabel='gpid-gts-z3 @total', ylabel='csp.native @execution')
#Grapher07 = grapher.SerieCompareGrapher('&0.ttime', '&1.itime', float, float, title='Seconds of exec comparisons for size 1 generation to 15"', xlabel='gpid-gts-z3 @total', ylabel='csp.native @interrupt')
# --------------------
#Grapher09 = grapher.SerieCompareGrapher('&5.implicates', '&6.potential-primes', int, int, title='Number of implicates of any size generated in 15"', xlabel='gpid-gts-z3', ylabel='csp.native @potential-primes')
#Grapher10 = grapher.SerieCompareGrapher('&5.implicates', '&6.primes', int, int, title='Number of implicates of any size generated in 15"', xlabel='gpid-gts-z3', ylabel='csp.native @primes')
#Grapher11 = grapher.SerieCompareGrapher('&5.gtime', '&6.etime', float, float, title='Seconds of exec comparisons for size ? generation to 15"', xlabel='gpid-gts-z3 @generation', ylabel='csp.native @execution')
#Grapher12 = grapher.SerieCompareGrapher('&5.gtime', '&6.itime', float, float, title='Seconds of exec comparisons for size ? generation to 15"', xlabel='gpid-gts-z3 @generation', ylabel='csp.native @interrupt')
#Grapher13 = grapher.SerieCompareGrapher('&5.ttime', '&6.etime', float, float, title='Seconds of exec comparisons for size ? generation to 15"', xlabel='gpid-gts-z3 @total', ylabel='csp.native @execution')
#Grapher14 = grapher.SerieCompareGrapher('&5.ttime', '&6.itime', float, float, title='Seconds of exec comparisons for size ? generation to 15"', xlabel='gpid-gts-z3 @total', ylabel='csp.native @interrupt')
# --------------------
def reposit(pdata, r0, r1, glim):
    if r0 not in pdata and 1 not in pdata:
        return 2
    if r0 not in pdata:
        return 0
    if r1 not in pdata:
        return 1

    csp  = False
    gpid = False

    if 'potential-primes' in pdata[r1] and int(pdata[r1]['potential-primes'][0]) > 0:
        csp  = True
    if 'primes' in pdata[r1] and int(pdata[r1]['primes'][0]) > 0:
        csp  = True
    if 'implicates' in pdata[r0] and int(pdata[r0]['implicates'][0]) > glim:
        gpid = True

    if csp and gpid:
        return 5
    if csp:
        return 3
    if gpid:
        return 4
    return 6
# --------------------
#Grapher16 = grapher.ProblemCatSplitter(lambda x : reposit(x, 0, 1, 0), { 0:'<Broken:GPiD>', 1:'<Broken:cSP>', 2:'<Broken:Both>',   3:'cSP', 4:'GPiD', 5:'cSP + GPiD', 6:'None' }, title='Size 1 Generation in 15" - Example groups')
#Grapher17 = grapher.ProblemCatSplitter(lambda x : reposit(x, 0, 1, 1), { 0:'<Broken:GPiD>', 1:'<Broken:cSP>', 2:'<Broken:Both>',   3:'cSP', 4:'GPiD', 5:'cSP + GPiD', 6:'None' }, title='Size 1 Generation in 15" w/ strict GPiD - Example groups')
#Grapher18 = grapher.ProblemCatSplitter(lambda x : reposit(x, 5, 6, 0), { 0:'<Broken:GPiD>', 1:'<Broken:cSP>', 2:'<Broken:Both>',   3:'cSP', 4:'GPiD', 5:'cSP + GPiD', 6:'None' }, title='Size ? Generation in 15" - Example groups')
#Grapher19 = grapher.ProblemCatSplitter(lambda x : reposit(x, 5, 6, 1), { 0:'<Broken:GPiD>', 1:'<Broken:cSP>', 2:'<Broken:Both>',   3:'cSP', 4:'GPiD', 5:'cSP + GPiD', 6:'None' }, title='Size ? Generation in 15" w/ strict GPiD - Example groups')
# --------------------
def serie_splitter_2d(data):
    if data[0] > data[1]:
        return 0
    if data[0] < data[1]:
        return 1
    return 2
# --------------------
Grapher20 = grapher.SeriesCatSplitter(['&0.implicates', '&1.potential-primes'], serie_splitter_2d, { 0:'GPiD > cSP', 1:'GPiD < cSP', 2:'GPiD = cSP' }, typeconvs={0:int, 1:int}, title='More implicates generated on size 1 - 15"')
Grapher21 = grapher.SeriesCatSplitter(['&5.implicates', '&6.implicates'], serie_splitter_2d, { 0:'GPiD > cSP', 1:'GPiD < cSP', 2:'GPiD = cSP' }, typeconvs={0:int, 1:int}, title='More implicates generated on size ? - 15"')
# --------------------
StrictTimeFilter2 = grapher.ProblemFilter('&2.gtime', lambda x : float(x) > 15)
StrictTimeFilter7 = grapher.ProblemFilter('&7.gtime', lambda x : float(x) > 15)
ExistFilter0 = grapher.ProblemFilter('&0.implicates', lambda x : int(x) < 1)
ExistFilter2 = grapher.ProblemFilter('&2.implicates', lambda x : int(x) < 1)
ExistFilter5 = grapher.ProblemFilter('&5.implicates', lambda x : int(x) < 1)
ExistFilter7 = grapher.ProblemFilter('&7.implicates', lambda x : int(x) < 1)
OutOfClassFilter0 = grapher.ProblemMultiFilter(['&0.implicates', '&0.gtime'],
                                               lambda l : int(l[0]) == 1 and float(l[1]) > 15)
OutOfClassFilter5 = grapher.ProblemMultiFilter(['&5.implicates', '&5.gtime'],
                                               lambda l : int(l[0]) == 1 and float(l[1]) > 15)
# --------------------
Grapher22 = grapher.SerieHistogram('&0.implicates', int,
                                   filters=[ExistFilter0, OutOfClassFilter0],
                                   title='Generation of implicates of size 1 in 15"',
                                   xlabel='Number of implicates generated',
                                   ylabel='Number of examples')
Grapher23 = grapher.SerieHistogram('&5.implicates', int,
                                   filters=[ExistFilter5, OutOfClassFilter5],
                                   title='Generation of implicates of any size in 15"',
                                   xlabel='Number of implicates generated',
                                   ylabel='Number of examples')
Grapher24 = grapher.SerieHistogram('&2.gtime', float,
                                   filters=[StrictTimeFilter2, ExistFilter2],
                                   title='Generation of one implicate of size 1',
                                   xlabel='Time (in seconds) necessary to generate one implicate',
                                   ylabel='Number of examples')
Grapher25 = grapher.SerieHistogram('&7.gtime', float,
                                   filters=[StrictTimeFilter7, ExistFilter7],
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
def gen_Deviation_GPiD_cSP(refg, refc, crefd):
    def local_f(pdata):
        gcount = 0
        ccount = 0
        try:
            pdata.get_reference('&{ev}.broken'.format(ev=refc))
            return None
        except core.UndefinedEvaluationResultException:
            pass
        try:
            gcount = pdata.get_reference('&{ev}.implicates'.format(ev=refg))
        except core.UndefinedEvaluationResultException:
            gcount = 0
        try:
            ccount = pdata.get_reference('&{ev}.{dta}'.format(ev=refc, dta=crefd))
        except core.UndefinedEvaluationResultException as e:
            ccount = 0
        gcount = int(gcount)
        ccount = int(ccount)
        if gcount >= ccount:
            return None
        return ccount - gcount
    return local_f
# --------------------
def gen_cSP_nBrk(ref):
    def local_f(pdata):
        try:
            pdata.get_reference('&{ev}.broken'.format(ev=ref))
            return None
        except core.UndefinedEvaluationResultException:
            return pdata.problem_file
    return local_f
# --------------------
def gen_Who1st_count(refg, refc, fe1=True):
    def local_f(pdata):
        gcount = 0
        ccount = 0
        try:
            pdata.get_reference('&{ev}.broken'.format(ev=refc))
            return None
        except core.UndefinedEvaluationResultException:
            pass
        try:
            gcount = pdata.get_reference('&{ev}.implicates'.format(ev=refg))
            gtime  = pdata.get_reference('&{ev}.gtime'.format(ev=refg))
            if gtime > 15:
                gcount = 0
        except core.UndefinedEvaluationResultException:
            gcount = 0
        try:
            ccount = pdata.get_reference('&{ev}.potential-primes'.format(ev=refc))
        except core.UndefinedEvaluationResultException as e:
            ccount = 0
        gcount = int(gcount)
        ccount = int(ccount)
        if fe1:
            return True if gcount > ccount else None
        else:
            return True if ccount > gcount else None
    return local_f
# --------------------
Vx01 = grapher.ValueXtractor('Prop 0 GPiD Examples size 1', gen_GPiD_AL1Ex(0), lambda x : 1 - len(x)/2549)
Vx02 = grapher.ValueXtractor('Prop 0 GPiD Examples size ?', gen_GPiD_AL1Ex(5), lambda x : 1 - len(x)/2549)

Vx03 = grapher.ValueXtractor('All generated GPiD Examples size 1', gen_GPiD_AGEx(0), lambda x : len(x)/2549)
Vx04 = grapher.ValueXtractor('All generated GPiD Examples size ?', gen_GPiD_AGEx(5), lambda x : len(x)/2549)

Vx05 = grapher.ValueXtractor('Mean 1st S1 implicate gen-time u15', gen_GPiD_TimeU15Ex(2), stat.mean)
Vx06 = grapher.ValueXtractor('Mean 1st S? implicate gen-time u15', gen_GPiD_TimeU15Ex(7), stat.mean)
Vx07 = grapher.ValueXtractor('Median 1st S1 implicate gen-time u15', gen_GPiD_TimeU15Ex(2), stat.median)
Vx08 = grapher.ValueXtractor('Median 1st S? implicate gen-time u15', gen_GPiD_TimeU15Ex(7), stat.median)

# Three first : Actually no such examples
#Vx09 = grapher.ValueXtractor('Max  Deviation S1 when csp > gpid', gen_Deviation_GPiD_cSP(0, 1, 'potential-primes'), max)
#Vx10 = grapher.ValueXtractor('Mean Deviation S1 when csp > gpid', gen_Deviation_GPiD_cSP(0, 1, 'potential-primes'), stat.mean)
#Vx11 = grapher.ValueXtractor('Std  Deviation S1 when csp > gpid', gen_Deviation_GPiD_cSP(0, 1, 'potential-primes'), stat.stdev)
Vx12 = grapher.ValueXtractor('Max  Deviation S? when csp > gpid', gen_Deviation_GPiD_cSP(5, 6, 'implicates'), max)
Vx13 = grapher.ValueXtractor('Mean Deviation S? when csp > gpid', gen_Deviation_GPiD_cSP(5, 6, 'implicates'), stat.mean)
Vx14 = grapher.ValueXtractor('Std  Deviation S? when csp > gpid', gen_Deviation_GPiD_cSP(5, 6, 'implicates'), stat.stdev)
Vx15 = grapher.ValueXtractor('Prop of S? examples where csp > gpid', gen_Deviation_GPiD_cSP(5, 6, 'implicates'), lambda x : len(x)/337)

Vx16 = grapher.ValueXtractor('Prop of non broken S1 csp examples', gen_cSP_nBrk(1), lambda x : len(x)/2549)
Vx17 = grapher.ValueXtractor('Prop of non broken S? csp examples', gen_cSP_nBrk(6), lambda x : len(x)/2549)

Vx18 = grapher.ValueXtractor('GPiD First first @gtime', gen_Who1st_count(2, 3), len)
Vx19 = grapher.ValueXtractor('GPiD First first @ttime', gen_Who1st_count(2, 4), len)
Vx20 = grapher.ValueXtractor('cSP First first @gtime', gen_Who1st_count(2, 3, False), len)
Vx21 = grapher.ValueXtractor('cSP First first @ttime', gen_Who1st_count(2, 4, False), len)

Vx22 = grapher.ValueXtractor('cSP non Broken List', gen_cSP_nBrk(1), '\n'.join)
Vx23 = grapher.ValueXtractor('cSP non Broken List', gen_cSP_nBrk(6), '\n'.join)


Vx101 = grapher.ValueXtractor('Prop S1 1st generated under 0.05', gen_GPiD_TimeU15Ex(2),
                                  lambda x : len([l for l in x if l < 0.05])/2549)
Vx102 = grapher.ValueXtractor('Prop S? 1st generated under 0.05', gen_GPiD_TimeU15Ex(7),
                                  lambda x : len([l for l in x if l < 0.05])/2549)
Vx103 = grapher.ValueXtractor('Prop S1 1st generated under 0.1', gen_GPiD_TimeU15Ex(2),
                                  lambda x : len([l for l in x if l < 0.1])/2549)
Vx104 = grapher.ValueXtractor('Prop S? 1st generated under 0.1', gen_GPiD_TimeU15Ex(7),
                                  lambda x : len([l for l in x if l < 0.1])/2549)
Vx105 = grapher.ValueXtractor('Prop S1 1st generated under 0.5', gen_GPiD_TimeU15Ex(2),
                                  lambda x : len([l for l in x if l < 0.5])/2549)
Vx106 = grapher.ValueXtractor('Prop S? 1st generated under 0.5', gen_GPiD_TimeU15Ex(7),
                                  lambda x : len([l for l in x if l < 0.5])/2549)
Vx107 = grapher.ValueXtractor('Prop S1 1st generated under 1', gen_GPiD_TimeU15Ex(2),
                                  lambda x : len([l for l in x if l < 1])/2549)
Vx108 = grapher.ValueXtractor('Prop S? 1st generated under 1', gen_GPiD_TimeU15Ex(7),
                                  lambda x : len([l for l in x if l < 1])/2549)
Vx109 = grapher.ValueXtractor('Prop S1 1st generated under 5', gen_GPiD_TimeU15Ex(2),
                                  lambda x : len([l for l in x if l < 5])/2549)
Vx110 = grapher.ValueXtractor('Prop S? 1st generated under 5', gen_GPiD_TimeU15Ex(7),
                                  lambda x : len([l for l in x if l < 5])/2549)
# --------------------
# Script
# --------------------
script = core.ScriptBox()

script.add_command(core.ImportContextCommand(sys.argv[1]))
script.add_command(core.ImportContextCommand(sys.argv[2], 'problems', [1,6]))
script.add_command(core.ImportContextCommand(sys.argv[3], 'problems', [0,2,5,7]))

#script.add_command(core.GraphCommand('problems', Grapher01, '01.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher03, '03.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher04, '04.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher05, '05.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher06, '06.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher07, '07.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher09, '09.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher10, '10.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher11, '11.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher12, '12.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher13, '13.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher14, '14.pdf'))

#script.add_command(core.GraphCommand('problems', Grapher15, '15.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher16, '16.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher17, '17.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher18, '18.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher19, '19.pdf'))

#script.add_command(core.GraphCommand('problems', Grapher20, '20.pdf'))
#script.add_command(core.GraphCommand('problems', Grapher21, '21.pdf'))

script.add_command(core.GraphCommand('problems', Grapher02, '02.pdf'))
script.add_command(core.GraphCommand('problems', Grapher08, '08.pdf'))

script.add_command(core.GraphCommand('problems', Grapher22, '22.pdf'))
script.add_command(core.GraphCommand('problems', Grapher23, '23.pdf'))
script.add_command(core.GraphCommand('problems', Grapher24, '24.pdf'))
script.add_command(core.GraphCommand('problems', Grapher25, '25.pdf'))

script.add_command(core.ExtractCommand('problems', Vx01))
script.add_command(core.ExtractCommand('problems', Vx02))
script.add_command(core.ExtractCommand('problems', Vx03))
script.add_command(core.ExtractCommand('problems', Vx04))
script.add_command(core.ExtractCommand('problems', Vx05))
script.add_command(core.ExtractCommand('problems', Vx06))
script.add_command(core.ExtractCommand('problems', Vx07))
script.add_command(core.ExtractCommand('problems', Vx08))

#script.add_command(core.ExtractCommand('problems', Vx09))
#script.add_command(core.ExtractCommand('problems', Vx10))
#script.add_command(core.ExtractCommand('problems', Vx11))
script.add_command(core.ExtractCommand('problems', Vx12))
script.add_command(core.ExtractCommand('problems', Vx13))
script.add_command(core.ExtractCommand('problems', Vx14))
script.add_command(core.ExtractCommand('problems', Vx15))

script.add_command(core.ExtractCommand('problems', Vx16))
script.add_command(core.ExtractCommand('problems', Vx17))

script.add_command(core.ExtractCommand('problems', Vx18))
script.add_command(core.ExtractCommand('problems', Vx19))
script.add_command(core.ExtractCommand('problems', Vx20))
script.add_command(core.ExtractCommand('problems', Vx21))

#script.add_command(core.ExtractCommand('problems', Vx22))
#script.add_command(core.ExtractCommand('problems', Vx23))

script.add_command(core.ExtractCommand('problems', Vx101))
script.add_command(core.ExtractCommand('problems', Vx102))
script.add_command(core.ExtractCommand('problems', Vx103))
script.add_command(core.ExtractCommand('problems', Vx104))
script.add_command(core.ExtractCommand('problems', Vx105))
script.add_command(core.ExtractCommand('problems', Vx106))
script.add_command(core.ExtractCommand('problems', Vx107))
script.add_command(core.ExtractCommand('problems', Vx108))
script.add_command(core.ExtractCommand('problems', Vx109))
script.add_command(core.ExtractCommand('problems', Vx110))

script.execute()
# --------------------
