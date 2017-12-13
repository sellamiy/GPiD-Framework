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

ProblemRequirement = evaluator.FileExistsRequirement()
AbduceRequirement  = evaluator.LinkedFileExistsRequirement('abduce', [('.smt2', '.abd')])

BasicEvaluation = evaluator.ToolEvaluation('$0')
FirstEvaluation = evaluator.ToolEvaluation('$0 --implicate-limit=1')
Size1Evaluation = evaluator.ToolEvaluation('$0 --implicate-size-limit=1')

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

GPiDEvaluator.add_requirement('<&file>', ProblemRequirement)
GPiDEvaluator.add_requirement('abduce', AbduceRequirement)

GPiDEvaluator.add_option('timeout', TimeoutOption)

GPiDEvaluator.add_result('implicates', ImplicateCount)
GPiDEvaluator.add_result('nodes', NodeCount)
GPiDEvaluator.add_result('gtime', GenerationTime)
GPiDEvaluator.add_result('ttime', TotalTime)
# --------------------
# Problem Set
# --------------------
ProblemSet = core.ProblemSet()
stream = open('smt-examples.txt')
ProblemSet.add_file_list([ fn.strip() for fn in stream.readlines() if fn.strip != '' ])
stream.close()
# --------------------
# Script
# --------------------
script = core.ScriptBox()

script.add_variable('gpid', GPiDEvaluator)
script.add_variable('problems', ProblemSet)

script.add_command(core.EvaluationCommand(0, 'problems', 'gpid', 'first'))
script.add_command(core.EvaluationCommand(1, 'problems', 'gpid', 'basic'))
script.add_command(core.EvaluationCommand(2, 'problems', 'gpid', 'first', [core.OptionData('timeout', { 1 : 10, 2 : 10 })]))
script.add_command(core.EvaluationCommand(3, 'problems', 'gpid', 'first', [core.OptionData('timeout', { 1 : '&2.gtime', 2 : 100 })]))

script.add_command(core.ExportContextCommand())

script.execute()
# --------------------
