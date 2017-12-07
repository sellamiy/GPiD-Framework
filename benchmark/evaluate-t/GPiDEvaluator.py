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
from Evaluator import Evaluator
# --------------------------------------
class GPiDEvaluator(Evaluator):

    def __init__(self, executable, timeout, evaluations, problems):
        Evaluator.__init__(self, executable, timeout, evaluations, problems)

    def _compute_abducible_filename(self, problem):
        return self._switch_filename_extension(problem, 'abduce')

    def _compute_log_filename(self, problem, evaluation):
        return self._switch_filename_extension(problem, 'gpid.%s.log' % evaluation)

    def _generate_command__all(self, problem):
        return ['timeout', str(self.timeout*2),
                self.executable,
                '-i', '%s' % problem,
                '-l', self._compute_abducible_filename(problem),
                '--time-limit=%i' % self.timeout]
    def _generate_command_size_1(self, problem):
        return ['timeout', str(self.timeout*2),
                self.executable,
                '-i', '%s' % problem,
                '-l', self._compute_abducible_filename(problem),
                '--time-limit=%i' % self.timeout,
                '--implicate-size-limit=1']
    def _generate_command_single(self, problem):
        return ['timeout', str(self.timeout*2),
                self.executable,
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
