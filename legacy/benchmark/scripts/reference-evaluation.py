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
# GPiD Solver
# --------------------
GPiDEvaluator = evaluator.ToolEvaluator()
GPiDEvaluator.set_executable('./bin/gpid-gts-z3')
GPiDEvaluator.set_format('$0 -i $1 -l $abduce')

AbduceGenerator = evaluator.ToolRequirementGeneratorFileByTool('../utils/converters/smt2abduce/Smt2AbduceGenerator.py', 'timeout 180 $0 $s', [])

ProblemRequirement = evaluator.FileExistsRequirement()
AbduceRequirement  = evaluator.LinkedFileExistsRequirement('abduce', [('.smt2', '.abduce')])
AbduceRequirement.set_generator(AbduceGenerator)

BasicEvaluation = evaluator.ToolEvaluation('$0')
FirstEvaluation = evaluator.ToolEvaluation('$0 --implicate-limit=1')
Size1Evaluation = evaluator.ToolEvaluation('$0 --implicate-size-limit=1')
F1Sz1Evaluation = evaluator.ToolEvaluation('$0 --implicate-limit=1 --implicate-size-limit=1')

TimeoutOption = evaluator.ToolOption('timeout $2 $0 --time-limit=$1', 2)

ImplicateCount = evaluator.ToolResult()
NodeCount      = evaluator.ToolResult()
GenerationTime = evaluator.ToolResult()
TotalTime      = evaluator.ToolResult()

ImplicateCount.add_matcher('$* Number of implicates generated : $!')
NodeCount     .add_matcher('$* Number of nodes explored : $!')
GenerationTime.add_matcher('$* Generation time : $! ms')
TotalTime     .add_matcher('$* Total time : $! ms')

GenerationTime.add_postop(lambda x : float(x)/1000)
TotalTime     .add_postop(lambda x : float(x)/1000)

GPiDEvaluator.add_evaluation('basic', BasicEvaluation)
GPiDEvaluator.add_evaluation('first', FirstEvaluation)
GPiDEvaluator.add_evaluation('size1', Size1Evaluation)
GPiDEvaluator.add_evaluation('first+size1', F1Sz1Evaluation)

GPiDEvaluator.add_requirement('<&file>', ProblemRequirement)
GPiDEvaluator.add_requirement('abduce', AbduceRequirement)

GPiDEvaluator.add_option('timeout', TimeoutOption)

GPiDEvaluator.add_result('implicates', ImplicateCount)
GPiDEvaluator.add_result('nodes', NodeCount)
GPiDEvaluator.add_result('gtime', GenerationTime)
GPiDEvaluator.add_result('ttime', TotalTime)
# --------------------
# cSP Solver
# --------------------
cSPEvaluator = evaluator.ToolEvaluator()
cSPEvaluator.set_executable('/home/mrcoco/Solvers/SophieSolvers/csp/csp.native')
cSPEvaluator.set_format('$0 -max-depth 1 $tptp')

TptpRequirement  = evaluator.LinkedFileExistsRequirement('tptp', [('.smt2', '_cnf.tptp')])

BasicEvaluation = evaluator.ToolEvaluation('$0')
Size1Evaluation = evaluator.ToolEvaluation('$0 -max-size 1')

TimeoutOption = evaluator.ToolOption('timeout $1 $0', 1)

ImplicateCount      = evaluator.ToolResult()
PotentialPrimeCount = evaluator.ToolResult()
ActualPrimeCount    = evaluator.ToolResult()
ExecutionTime       = evaluator.ToolResult()
InterruptionTime    = evaluator.ToolResult()
Broken              = evaluator.ToolResult()

ImplicateCount     .add_matcher('number of implicates generated: $!')
PotentialPrimeCount.add_matcher('number of potential prime implicates: $!')
ActualPrimeCount   .add_matcher('found $! prime implicates')
ExecutionTime      .add_matcher('execution time: $! seconds')
InterruptionTime   .add_matcher('$* TIMEOUT after $! seconds')
Broken             .add_matcher('Fatal error: $!')

cSPEvaluator.add_evaluation('basic', BasicEvaluation)
cSPEvaluator.add_evaluation('size1', Size1Evaluation)

cSPEvaluator.add_requirement('tptp', TptpRequirement)

cSPEvaluator.add_option('timeout', TimeoutOption)

cSPEvaluator.add_result('implicates', ImplicateCount)
cSPEvaluator.add_result('potential-primes', PotentialPrimeCount)
cSPEvaluator.add_result('primes', ActualPrimeCount)
cSPEvaluator.add_result('etime', ExecutionTime)
cSPEvaluator.add_result('itime', InterruptionTime)
cSPEvaluator.add_result('broken', Broken)
# --------------------
# Problem Set
# --------------------
ProblemSet = core.ProblemSet()
stream = open('/home/mrcoco/QF_UF.Sat.txt')
ProblemSet.add_file_list([ fn.strip() for fn in stream.readlines() if fn.strip != '' ])
stream.close()
# --------------------
# Script
# --------------------
script = core.ScriptBox()

script.add_variable('gpid', GPiDEvaluator)
script.add_variable('csp', cSPEvaluator)
script.add_variable('problems', ProblemSet)

#script.add_command(core.EvaluationCommand(0, 'problems', 'gpid', 'size1'      , [core.OptionData('timeout', { 1 : 15, 2 : 30 })]))
script.add_command(core.EvaluationCommand(1, 'problems', 'csp' , 'size1'      , [core.OptionData('timeout', { 1 : 15         })]))

#script.add_command(core.EvaluationCommand(2, 'problems', 'gpid', 'first+size1', [core.OptionData('timeout', { 1 : 15, 2 : 30 })]))
#script.add_command(core.EvaluationCommand(3, 'problems', 'csp' , 'size1'      , [core.OptionData('timeout', { 1 : '&2.gtime' })]))
#script.add_command(core.EvaluationCommand(4, 'problems', 'csp' , 'size1'      , [core.OptionData('timeout', { 1 : '&2.ttime' })]))

#script.add_command(core.EvaluationCommand(5, 'problems', 'gpid', 'basic'      , [core.OptionData('timeout', { 1 : 15, 2 : 30 })]))
script.add_command(core.EvaluationCommand(6, 'problems', 'csp' , 'basic'      , [core.OptionData('timeout', { 1 : 15         })]))

script.add_command(core.EvaluationCommand(7, 'problems', 'gpid', 'first'      , [core.OptionData('timeout', { 1 : 15, 2 : 30 })]))

script.add_command(core.ExportContextCommand())

script.execute()
# --------------------
