#!/usr/bin/env python3
# --------------------------------------
# Multigrapher for smt problems
# --------------------------------------
import sys, os
import ast
import argparse
# --------------------------------------
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
# --------------------------------------
from colorama import Fore, Style
# --------------------------------------
def log_local_intro(intro):
    sys.stderr.write('> %s - ' % intro)
    sys.stderr.flush()
def log_local_info(info):
    sys.stderr.write('%s - ' % info)
    sys.stderr.flush()
def log_local_success():
    sys.stderr.write('%sok%s\n' % (Fore.GREEN, Style.RESET_ALL))
def log_local_failure():
    sys.stderr.write('%sfailed%s\n' % (Fore.RED, Style.RESET_ALL))
# --------------------------------------
class ProblemResults:
    def __init__(self, problem):
        self.problem = problem
        self.results = { }

    def load_results(self, solvers, evaluations):
        for solver in solvers:
            for evaluation in evaluations:
                try:
                    logfile = self._compute_log_filename(solver, evaluation)
                    self.results[solver, evaluation] = self._read_results(logfile)
                except:
                    log_local_intro('loading')
                    log_local_info(logfile)
                    log_local_failure()
                    pass

    def _read_results(self, logfile):
        logstream = open(logfile, 'r')
        results = ast.literal_eval(logstream.read().strip())
        logstream.close()
        return results

    def _switch_filename_extension(self, new_extension):
        filepath = os.path.dirname(self.problem)
        filename = os.path.basename(self.problem)
        filename = '%s.%s' % (os.path.splitext(filename)[0], new_extension)
        return os.path.join(filepath, filename)

    def _compute_log_filename(self, solver, evaluation):
        return self._switch_filename_extension('%s.%s.log' % (solver, evaluation))
# --------------------------------------
class MultiGrapher:

    def __init__(self, problems, solvers, evaluations):
        self.problems = { problem : ProblemResults(problem) for problem in problems }
        self.solvers = solvers
        self.evaluations = evaluations

    def load(self):
        for problem, data in self.problems.items():
            data.load_results(self.solvers, self.evaluations)

    def graph(self, graphs):
        for graph in graphs:
            self._handle_graph(graph)()

    def _handle_graph(self, graph):
        return {
            'execution-time-range' : self.graph_execution_time_range
        }[graph]

    def _compute_graphfile_name(self, graph, solver, evaluation):
        return 'mg-graph-%s.%s_%s.svg' % (graph, solver, evaluation)

    def graph_execution_time_range(self):
        for solver in self.solvers:
            for evaluation in self.evaluations:
                log_local_intro('generate execution time range graph')
                log_local_info(solver)
                log_local_info(evaluation)
                try:
                    self._graph_execution_time_range(solver, evaluation)
                    log_local_success()
                except:
                    log_local_failure()

    def _graph_execution_time_range(self, solver, evaluation):
        # Recovering time points
        clpoints = []
        for problem, data in self.problems.items():
            local = data.results[solver, evaluation]
            try:
                if solver == 'csp':
                    if local['total-time'] is not None:
                        time = float(local['total-time'].split()[0])
                    elif local['interruption-time'] is not None:
                        time = float(local['interruption-time'].split()[0])
                    else:
                        time = None
                elif solver == 'gpid':
                    time = float(local['generation-time'].split()[0])
            except:
                time = None
            clpoints.append(time)
        nnpoints = [ p for p in clpoints if p is not None ]
        failcpt = len([ p for p in clpoints if p is None ])
        # Graphing time points
        figure, (pl1, pl2) = plt.subplots(1, 2)
        pl1.set_title('Success time range')
        pl2.set_title('Failure range')

        pl1.hist(nnpoints)
        pl2.bar(0, (len(nnpoints),), 1, color='g')
        pl2.bar(0, (failcpt,), 1, bottom=(len(nnpoints),), color='r')
        # Export
        figure.savefig(self._compute_graphfile_name('execution-time-range', solver, evaluation))
        
# --------------------------------------
argparser = argparse.ArgumentParser(description='Example results multiGrapher')
argparser.add_argument('-i', '--input-problems', dest='problems',
                       metavar='<example>.smt2', type=str,
                       nargs='+', required=True,
                       help='example to analyze')
argparser.add_argument('-s', '--solvers', type=str, nargs='+', required=True,
                       choices=['gpid', 'csp'],
                       help='solvers that evaluated the problem')
argparser.add_argument('-e', '--evaluation-type', dest='evaluations',
                       type=str, nargs='+', required=True,
                       choices=['generate-all', 'generate-size-one'],
                       help='type of evaluation performed')
argparser.add_argument('-g', '--graph-targets', dest='graphs',
                       type=str, nargs='+', required=True,
                       choices=['execution-time-range'],
                       help='graph to generate')
# --------------------------------------
def main(opts):
    grapher = MultiGrapher(opts.problems, opts.solvers, opts.evaluations)
    grapher.load()
    grapher.graph(opts.graphs)
# --------------------------------------
if __name__ == '__main__':
    main(argparser.parse_args())
# --------------------------------------
