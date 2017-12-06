#!/usr/bin/env python3
# --------------------------------------
# Evaluate smt2 problems via GPiD-gTS
# --------------------------------------
import sys, os
import argparse
# --------------------------------------
from subprocess import check_output, STDOUT, CalledProcessError, TimeoutExpired
from colorama import Fore, Style
# --------------------------------------
class GPiDEvaluator:

    def __init__(self, executable, timeout, evaluations, problems):
        self.executable = executable
        self.timeout = timeout
        self.evaluations = evaluations
        self.problems = problems

    def add_problem(self, problem):
        self.problem_list.append(problem)

    def check(self):
        for problem in self.problems:
            self._check(problem)

    def _clear_file(self, filename):
        open(filename, 'w').close()

    def _switch_filename_extension(self, problem, new_extension):
        filepath = os.path.dirname(problem)
        filename = os.path.basename(problem)
        filename = '%s.%s' % (os.path.splitext(filename)[0], new_extension)
        return os.path.join(filepath, filename)

    def _compute_abducible_filename(self, problem):
        return self._switch_filename_extension(problem, 'abduce')

    def _compute_log_filename(self, problem, evaluation):
        return self._switch_filename_extension(problem, 'gpid.%s.log' % evaluation)

    def _prepare_filename_directory(self, filename):
        filepath = os.path.dirname(filename)
        if not os.path.exists(filepath):
            os.makedirs(filepath)

    def _generate_command__all(self, problem):
        return [self.executable,
                '-i', '%s' % problem,
                '-l', self._compute_abducible_filename(problem),
                '--time-limit=%i' % self.timeout]
    def _generate_command_size_1(self, problem):
        return [self.executable,
                '-i', '%s' % problem,
                '-l', self._compute_abducible_filename(problem),
                '--time-limit=%i' % self.timeout,
                '--implicate-size-limit=1']
    def _generate_command_single(self, problem):
        return [self.executable,
                '-i', '%s' % problem,
                '-l', self._compute_abducible_filename(problem),
                '--time-limit=%i' % self.timeout,
                '--implicate-limit=1']

    def _get_generator_function(self, evaluation):
        return {
                   'generate-all'      : self._generate_command__all,
                   'generate-one'      : self._generate_command_single,
                   'generate-size-one' : self._generate_command_size_1
               }[evaluation]

    def _parse_result_value(self, log, value):
        return [l for l in log.split('\n') if value in l][0].split(':')[1].strip()

    def _execute(self, command_generator, problem):
        command = command_generator(problem)
        results = {}
        try:
            cout = check_output(command, stderr=STDOUT)
            cout = cout.decode(sys.stdout.encoding)
            results['implicate-count'] = self._parse_result_value(cout, 'Number of implicates generated')
            results['node-count'] = self._parse_result_value(cout, 'Number of nodes explored')
            results['generation-time'] = self._parse_result_value(cout, 'Generation time')
            results['total-time'] = self._parse_result_value(cout, 'Total time')
            results['status'] = 'Complete'
        except CalledProcessError:
            results['status'] = 'ExecutionError'
        except IndexError:
            results['status'] = 'IndexError'
        return results

    def _log_result(self, problem, evaluation, results):
        logfile = self._compute_log_filename(problem, evaluation)
        self._prepare_filename_directory(logfile)
        logstream = open(logfile, 'w')
        logstream.write('%s\n' % results)
        logstream.close()

    def _check(self, problem):
        for evaluation in self.evaluations:
            results = self._execute(self._get_generator_function(evaluation), problem)
            self._log_result(problem, evaluation, results)
# --------------------------------------
argparser = argparse.ArgumentParser(description='Example evaluator for GPiD-gTs')
argparser.add_argument('problems', metavar='<example>.smt2', type=str, nargs='+',
                       help='example to evaluate')
argparser.add_argument('-g', '--gts-location', type=str, required=True,
                       help='location of the GPiD-gTs executable')
argparser.add_argument('-e', '--evaluation-type', dest='evaluations',
                       type=str, nargs='+', required=True,
                       choices=['generate-all', 'generate-one', 'generate-size-one'],
                       help='type of evaluation to perform')
argparser.add_argument('-t', '--timeout', type=int, default=3600,
                       help='timeout for an example (in seconds)')
# --------------------------------------
def main(opts):
    checker = GPiDEvaluator(opts.gts_location, opts.timeout, opts.evaluations, opts.problems)
    checker.check()
# --------------------------------------
if __name__ == '__main__':
    main(argparser.parse_args())
# --------------------------------------
